/*
Copyright (c) 2025 by the contributors listed below

The list is sorted by surname and formatted to allow easy grepping and
beautification by scripts.  The fields are: name (N), email (E), web-address
(W), PGP key ID and fingerprint (P), description (D), and snail-mail address
(S).

N: Guillaume Legris
W: http://www.thenesis.org

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

// __truncxfdf2 — long double (80-bit ext.) -> double (64-bit IEEE)
// i386 little-endian, soft-float friendly (aucune instr. x87/SSE).
// Rounding: nearest ties-to-even. Subnormaux (double) : flush-to-zero (simplifié).

#include <stdint.h>
#include <string.h>

static inline int clz64(uint64_t x) {
    return x ? __builtin_clzll(x) : 64;
}

double __truncxfdf2(long double a)
{
    // Read the 10 "real" bytes of the 80-bit extended (little-endian) format
    unsigned char raw[10];
    memcpy(raw, &a, 10);

    // Decompose: 64-bit mantissa (bit63 = integer-bit), SE = [sign(1) | exp(15)]
    uint64_t mant = ((uint64_t)raw[0])
                  | ((uint64_t)raw[1] << 8)
                  | ((uint64_t)raw[2] << 16)
                  | ((uint64_t)raw[3] << 24)
                  | ((uint64_t)raw[4] << 32)
                  | ((uint64_t)raw[5] << 40)
                  | ((uint64_t)raw[6] << 48)
                  | ((uint64_t)raw[7] << 56);
    uint16_t se   = (uint16_t)raw[8] | ((uint16_t)raw[9] << 8);

    const int sign = (se >> 15) & 1;
    int exp_ext    = se & 0x7FFF;                // extended exponent (bias 16383)

    const uint64_t INTBIT = 1ull << 63;         // 80-bit "integer" bit
    const int BIAS_EXT = 16383;
    const int BIAS_DBL = 1023;

    // Double constants
    const uint64_t DBL_INF  = 0x7FFull << 52;
    const uint64_t DBL_QNAN = (0x7FFull << 52) | (1ull << 51);

    // Zero (±)
    if (exp_ext == 0 && mant == 0) {
        uint64_t out = (uint64_t)sign << 63; // +0 ou -0
        double d; memcpy(&d, &out, sizeof d); return d;
    }

    // Inf / NaN (exp = 0x7FFF)
    if (exp_ext == 0x7FFF) {
        // Inf if mantissa == INTBIT (integer-bit=1, frac=0). Otherwhise NaN.
        uint64_t out = ((mant == INTBIT) ? DBL_INF : DBL_QNAN);
        out |= (uint64_t)sign << 63;
        double d; memcpy(&d, &out, sizeof d); return d;
    }

    // Normalize the mantissa to have INTBIT=1 and calculate the unbiased exponent e
    int e;              // unbiased exponent in base 2
    uint64_t sig;       // normalized significand with bit 63 = 1

    if (exp_ext == 0) {
        // Extended subnormal: integer-bit = 0, exp = 1 - BIAS_EXT after normalization
        if (mant == 0) { // already treated, but as a precaution
            uint64_t out = (uint64_t)sign << 63;
            double d; memcpy(&d, &out, sizeof d); return d;
        }
        int sh = clz64(mant);        //  mount the head bit in position 63
        sig = mant << sh;
        e = (1 - BIAS_EXT) - sh + 63;
    } else {
        //  Extended Normal: integer-bit must be 1
        sig = mant;
        e = exp_ext - BIAS_EXT;
        if (!(sig & INTBIT)) {
            // pathological case: repairs by normalizing
            int sh = clz64(sig);
            sig <<= sh;
            e -= sh - 63;
        }
    }

    // Conversion to double: we must produce 53 bits (1 implicit + 52 fraction).
    // We start from 'sig' (64 bits with bit63=1). Shift right by 11 to get 53 bits.
    uint64_t round_mask = (1ull << 11) - 1;     // bits lost for rounding
    uint64_t round_bits = sig & round_mask;
    uint64_t mant53     = sig >> 11;            // 53 bits : [1].[52 frac]

    // Rounding "nearest, ties-to-even"
    const uint64_t HALF = 1ull << 10;           // 0b10000000000
    if (round_bits > HALF || (round_bits == HALF && (mant53 & 1)))
        mant53++;

    // Rounding Overflow Management (ex: 1.111.. -> 10.000..)
    if (mant53 == (1ull << 53)) {
        mant53 >>= 1;
        e += 1;
    }

    //  Calculating the double exponent
    int E = e + BIAS_DBL;

    // Overflow -> Inf
    if (E >= 0x7FF) {
        uint64_t out = ((uint64_t)sign << 63) | DBL_INF;
        double d; memcpy(&d, &out, sizeof d); return d;
    }

    // Subflow to double subnormal? (simplified implementation: flush-to-zero)
    if (E <= 0) {
        uint64_t out = (uint64_t)sign << 63; // ±0
        double d; memcpy(&d, &out, sizeof d); return d;
    }

    // Construct the IEEE-754 encoding of the double
    uint64_t frac52 = mant53 & ((1ull << 52) - 1); // remove the implicit bit
    uint64_t out = ((uint64_t)sign << 63) | ((uint64_t)E << 52) | frac52;

    double d; memcpy(&d, &out, sizeof d); return d;
}

long double __extenddfxf2(double a)
{
    // Decompose the double (IEEE-754)
    uint64_t ubits;
    memcpy(&ubits, &a, sizeof ubits);

    const int sign = (int)(ubits >> 63);
    const unsigned exp = (unsigned)((ubits >> 52) & 0x7FFu);
    uint64_t frac = ubits & ((UINT64_C(1) << 52) - 1);

    // Constants for 80-bit extended (i386)
    const int BIAS_DBL = 1023;
    const int BIAS_EXT = 16383;
    const uint64_t INTBIT = UINT64_C(1) << 63;      // explicit bit "integer"
    const uint16_t EXP_INF_NAN = 0x7FFF;            // max exponent (Inf/NaN)

    // 10-byte buffer (64-bit LE mantissa, then 16-bit LE SE)
    unsigned char raw[10];
    uint64_t mant = 0;   // 64 bits: bit63 = integer-bit, 62..0 = fraction
    uint16_t se  = 0;    // [sign(1) | exp(15)]

    if (exp == 0 && frac == 0) {
        // ±0
        mant = 0;
        se = (uint16_t)(sign << 15);
    }
    else if (exp == 0x7FF) {
        // Inf / NaN
        se = (uint16_t)((sign << 15) | EXP_INF_NAN);
        if (frac == 0) {
            // ±Inf : integer-bit = 1, fraction = 0
            mant = INTBIT;
        } else {
            // NaN : exponent max, integer-bit = 1, quiet-bit = 1, payload aligné
            // We roughly map the payload of the double (52b) into the high bits
            mant  = INTBIT;
            mant |= UINT64_C(1) << 62;                 // qNaN
            mant |= frac << (62 - 51);                 // payload (truncation if necessary)
        }
    }
    else if (exp == 0) {
        // Double Subnormal: Normalize frac to construct an extended normal
        // We raise the implicit 1 by shifting, and correct the exponent.
        // (frac != 0 here)
        int sh = 0;
        // Bring 1 to position bit51
        while ((frac & (UINT64_C(1) << 51)) == 0) {
            frac <<= 1;
            sh++;
        }
        // Now value = 1.frac * 2^(1 - BIAS_DBL - sh)
        const int e = (1 - BIAS_DBL) - sh;
        const int Eext = e + BIAS_EXT;

        se = (uint16_t)((sign << 15) | (Eext & 0x7FFF));
        // Mantissa 80-bit : integer-bit = 1, fraction (63 bits) = (frac without bit51) aligned
        const uint64_t frac_51 = frac & ((UINT64_C(1) << 51) - 1); // remove the leading 1
        mant = INTBIT | (frac_51 << (63 - 51));                    // shift of 12? -> (63-51)=12
    }
    else {
        // Normal double
        const int e = (int)exp - BIAS_DBL;
        const int Eext = e + BIAS_EXT;

        se = (uint16_t)((sign << 15) | (Eext & 0x7FFF));
        // 80-bit mantissa: explicit integer-bit + fraction of double (52b) aligned to 63b
        mant = INTBIT | (frac << (63 - 52));   // (63-52)=11
    }

    // Write 80-bit extended format (10 bytes) in little-endian
    raw[0] = (unsigned char)(mant);
    raw[1] = (unsigned char)(mant >> 8);
    raw[2] = (unsigned char)(mant >> 16);
    raw[3] = (unsigned char)(mant >> 24);
    raw[4] = (unsigned char)(mant >> 32);
    raw[5] = (unsigned char)(mant >> 40);
    raw[6] = (unsigned char)(mant >> 48);
    raw[7] = (unsigned char)(mant >> 56);
    raw[8] = (unsigned char)(se);
    raw[9] = (unsigned char)(se >> 8);

    // Build the long double exit
    long double out = 0.0L;
    // Copy of the 10 useful bytes; the padding (12/16 bytes) remains zero.
    memcpy(&out, raw, 10);
    return out;
}
