/*
Copyright (c) 2009-2025 by the contributors listed below

This file is a partial list of people who have contributed to the LLVM/CompilerRT
project.  If you have contributed a patch or made some other contribution to
LLVM/CompilerRT, please submit a patch to this file to add yourself, and it will be
done!

The list is sorted by surname and formatted to allow easy grepping and
beautification by scripts.  The fields are: name (N), email (E), web-address
(W), PGP key ID and fingerprint (P), description (D), and snail-mail address
(S).

N: Craig van Vliet
E: cvanvliet@auroraux.org
W: http://www.auroraux.org
D: Code style and Readability fixes.

N: Edward O'Callaghan
E: eocallaghan@auroraux.org
W: http://www.auroraux.org
D: CMake'ify Compiler-RT build system
D: Maintain Solaris & AuroraUX ports of Compiler-RT

N: Howard Hinnant
E: hhinnant@apple.com
D: Architect and primary author of compiler-rt

N: Guillaume Legris
W: http://www.thenesis.org
D: Decouple from LLVM

N: Mathieu Legris
W: http://www.thenesis.org
D: Decouple from LLVM, Code style and Readability fixes

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

#include "soft_float_internal_types.h"

#include <float.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>

typedef uint32_t rep_t;
typedef int32_t srep_t;
typedef float fp_t;
#define REP_C(a) UINT32_C(a)
#define significandBits 23

static inline int rep_clz(rep_t a) {
    return __builtin_clz(a);
}

// 32x32 --> 64 bit multiply
static inline void wideMultiply(rep_t a, rep_t b, rep_t *hi, rep_t *lo) {
    const uint64_t product = (uint64_t)a*b;
    *hi = product >> 32;
    *lo = product;
}

#define typeWidth       ((int) sizeof(rep_t)*CHAR_BIT)
#define exponentBits    (typeWidth - significandBits - 1)
#define maxExponent     ((1 << exponentBits) - 1)
#define exponentBias    (maxExponent >> 1)

#define implicitBit     (REP_C(1) << significandBits)
#define significandMask (implicitBit - 1U)
#define signBit         (REP_C(1) << (significandBits + exponentBits))
#define absMask         (signBit - 1U)
#define exponentMask    (absMask ^ significandMask)
#define oneRep          ((rep_t)exponentBias << significandBits)
#define infRep          exponentMask
#define quietBit        (implicitBit >> 1)
#define qnanRep         (exponentMask | quietBit)

static inline rep_t toRep(fp_t x) {
    const union { fp_t f; rep_t i; } rep = {.f = x};
    return rep.i;
}

static inline fp_t fromRep(rep_t x) {
    const union { fp_t f; rep_t i; } rep = {.i = x};
    return rep.f;
}

static inline int normalize(rep_t *significand) {
    const int shift = rep_clz(*significand) - rep_clz(implicitBit);
    *significand <<= shift;
    return 1 - shift;
}

static inline void wideLeftShift(rep_t *hi, rep_t *lo, int count) {
    *hi = *hi << count | *lo >> (typeWidth - count);
    *lo = *lo << count;
}

static inline void wideRightShiftWithSticky(rep_t *hi, rep_t *lo, int count) {
    if (count < typeWidth) {
        const bool sticky = *lo << (typeWidth - count);
        *lo = *hi << (typeWidth - count) | *lo >> count | sticky;
        *hi = *hi >> count;
    }
    else if (count < 2*typeWidth) {
        const bool sticky = *hi << (2*typeWidth - count) | *lo;
        *lo = *hi >> (count - typeWidth) | sticky;
        *hi = 0;
    } else {
        const bool sticky = *hi | *lo;
        *lo = sticky;
        *hi = 0;
    }
}

//--------------------------------------------------------------------------------
// Neg.
//--------------------------------------------------------------------------------
fp_t __negsf2(fp_t a) {
    return fromRep(toRep(a) ^ signBit);
}

//--------------------------------------------------------------------------------
// Add / sub.
//--------------------------------------------------------------------------------
fp_t __addsf3(fp_t a, fp_t b) {

    rep_t aRep = toRep(a);
    rep_t bRep = toRep(b);
    const rep_t aAbs = aRep & absMask;
    const rep_t bAbs = bRep & absMask;
    
    // Detect if a or b is zero, infinity, or NaN.
    if (aAbs - 1U >= infRep - 1U || bAbs - 1U >= infRep - 1U) {
        
        // NaN + anything = qNaN
        if (aAbs > infRep) return fromRep(toRep(a) | quietBit);
        // anything + NaN = qNaN
        if (bAbs > infRep) return fromRep(toRep(b) | quietBit);
        
        if (aAbs == infRep) {
            // +/-infinity + -/+infinity = qNaN
            if ((toRep(a) ^ toRep(b)) == signBit) return fromRep(qnanRep);
            // +/-infinity + anything remaining = +/- infinity
            else return a;
        }
        
        // anything remaining + +/-infinity = +/-infinity
        if (bAbs == infRep) return b;
        
        // zero + anything = anything
        if (!aAbs) {
            // but we need to get the sign right for zero + zero
            if (!bAbs) return fromRep(toRep(a) & toRep(b));
            else return b;
        }
        
        // anything + zero = anything
        if (!bAbs) return a;
    }
    
    // Swap a and b if necessary so that a has the larger absolute value.
    if (bAbs > aAbs) {
        const rep_t temp = aRep;
        aRep = bRep;
        bRep = temp;
    }
    
    // Extract the exponent and significand from the (possibly swapped) a and b.
    int aExponent = aRep >> significandBits & maxExponent;
    int bExponent = bRep >> significandBits & maxExponent;
    rep_t aSignificand = aRep & significandMask;
    rep_t bSignificand = bRep & significandMask;
    
    // Normalize any denormals, and adjust the exponent accordingly.
    if (aExponent == 0) aExponent = normalize(&aSignificand);
    if (bExponent == 0) bExponent = normalize(&bSignificand);
    
    // The sign of the result is the sign of the larger operand, a.  If they
    // have opposite signs, we are performing a subtraction; otherwise addition.
    const rep_t resultSign = aRep & signBit;
    const bool subtraction = (aRep ^ bRep) & signBit;
    
    // Shift the significands to give us round, guard and sticky, and or in the
    // implicit significand bit.  (If we fell through from the denormal path it
    // was already set by normalize( ), but setting it twice won't hurt
    // anything.)
    aSignificand = (aSignificand | implicitBit) << 3;
    bSignificand = (bSignificand | implicitBit) << 3;
    
    // Shift the significand of b by the difference in exponents, with a sticky
    // bottom bit to get rounding correct.
    const int align = aExponent - bExponent;
    if (align) {
        if (align < typeWidth) {
            const bool sticky = bSignificand << (typeWidth - align);
            bSignificand = bSignificand >> align | sticky;
        } else {
            bSignificand = 1; // sticky; b is known to be non-zero.
        }
    }
    
    if (subtraction) {
        aSignificand -= bSignificand;
        
        // If a == -b, return +zero.
        if (aSignificand == 0) return fromRep(0);
        
        // If partial cancellation occured, we need to left-shift the result
        // and adjust the exponent:
        if (aSignificand < implicitBit << 3) {
            const int shift = rep_clz(aSignificand) - rep_clz(implicitBit << 3);
            aSignificand <<= shift;
            aExponent -= shift;
        }
    }
    
    else /* addition */ {
        aSignificand += bSignificand;
        
        // If the addition carried up, we need to right-shift the result and
        // adjust the exponent:
        if (aSignificand & implicitBit << 4) {
            const bool sticky = aSignificand & 1;
            aSignificand = aSignificand >> 1 | sticky;
            aExponent += 1;
        }
    }
    
    // If we have overflowed the type, return +/- infinity:
    if (aExponent >= maxExponent) return fromRep(infRep | resultSign);
    
    if (aExponent <= 0) {
        // Result is denormal before rounding; the exponent is zero and we
        // need to shift the significand.
        const int shift = 1 - aExponent;
        const bool sticky = aSignificand << (typeWidth - shift);
        aSignificand = aSignificand >> shift | sticky;
        aExponent = 0;
    }
    
    // Low three bits are round, guard, and sticky.
    const int roundGuardSticky = aSignificand & 0x7;
    
    // Shift the significand into place, and mask off the implicit bit.
    rep_t result = aSignificand >> 3 & significandMask;
    
    // Insert the exponent and sign.
    result |= (rep_t)aExponent << significandBits;
    result |= resultSign;
    
    // Final rounding.  The result may overflow to infinity, but that is the
    // correct result in that case.
    if (roundGuardSticky > 0x4) result++;
    if (roundGuardSticky == 0x4) result += result & 1;
    return fromRep(result);
}

// Subtraction: flip the sign bit of b and add.
fp_t __subsf3(fp_t a, fp_t b) {
    return __addsf3(a, fromRep(toRep(b) ^ signBit));
}

//--------------------------------------------------------------------------------
// Multiplication with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
fp_t __mulsf3(fp_t a, fp_t b) {
    const unsigned int aExponent = toRep(a) >> significandBits & maxExponent;
    const unsigned int bExponent = toRep(b) >> significandBits & maxExponent;
    const rep_t productSign = (toRep(a) ^ toRep(b)) & signBit;
    
    rep_t aSignificand = toRep(a) & significandMask;
    rep_t bSignificand = toRep(b) & significandMask;
    int scale = 0;
    
    // Detect if a or b is zero, denormal, infinity, or NaN.
    if (aExponent-1U >= maxExponent-1U || bExponent-1U >= maxExponent-1U) {
        
        const rep_t aAbs = toRep(a) & absMask;
        const rep_t bAbs = toRep(b) & absMask;
        
        // NaN * anything = qNaN
        if (aAbs > infRep) return fromRep(toRep(a) | quietBit);
        // anything * NaN = qNaN
        if (bAbs > infRep) return fromRep(toRep(b) | quietBit);
        
        if (aAbs == infRep) {
            // infinity * non-zero = +/- infinity
            if (bAbs) return fromRep(aAbs | productSign);
            // infinity * zero = NaN
            else return fromRep(qnanRep);
        }
        
        if (bAbs == infRep) {
            // non-zero * infinity = +/- infinity
            if (aAbs) return fromRep(bAbs | productSign);
            // zero * infinity = NaN
            else return fromRep(qnanRep);
        }
        
        // zero * anything = +/- zero
        if (!aAbs) return fromRep(productSign);
        // anything * zero = +/- zero
        if (!bAbs) return fromRep(productSign);
        
        // one or both of a or b is denormal, the other (if applicable) is a
        // normal number.  Renormalize one or both of a and b, and set scale to
        // include the necessary exponent adjustment.
        if (aAbs < implicitBit) scale += normalize(&aSignificand);
        if (bAbs < implicitBit) scale += normalize(&bSignificand);
    }
    
    // Or in the implicit significand bit.  (If we fell through from the
    // denormal path it was already set by normalize( ), but setting it twice
    // won't hurt anything.)
    aSignificand |= implicitBit;
    bSignificand |= implicitBit;
    
    // Get the significand of a*b.  Before multiplying the significands, shift
    // one of them left to left-align it in the field.  Thus, the product will
    // have (exponentBits + 2) integral digits, all but two of which must be
    // zero.  Normalizing this result is just a conditional left-shift by one
    // and bumping the exponent accordingly.
    rep_t productHi, productLo;
    wideMultiply(aSignificand, bSignificand << exponentBits,
                 &productHi, &productLo);
    
    int productExponent = aExponent + bExponent - exponentBias + scale;
    
    // Normalize the significand, adjust exponent if needed.
    if (productHi & implicitBit) productExponent++;
    else wideLeftShift(&productHi, &productLo, 1);
    
    // If we have overflowed the type, return +/- infinity.
    if (productExponent >= maxExponent) return fromRep(infRep | productSign);
    
    if (productExponent <= 0) {
        // Result is denormal before rounding, the exponent is zero and we
        // need to shift the significand.
        wideRightShiftWithSticky(&productHi, &productLo, 1 - productExponent);
    }
    
    else {
        // Result is normal before rounding; insert the exponent.
        productHi &= significandMask;
        productHi |= (rep_t)productExponent << significandBits;
    }
    
    // Insert the sign of the result:
    productHi |= productSign;
    
    // Final rounding.  The final result may overflow to infinity, or underflow
    // to zero, but those are the correct results in those cases.
    if (productLo > signBit) productHi++;
    if (productLo == signBit) productHi += productHi & 1;
    return fromRep(productHi);
}

//--------------------------------------------------------------------------------
// Implements single-precision soft-float division
// with the IEEE-754 default rounding (to nearest, ties to even).
//
// For simplicity, this implementation currently flushes denormals to zero.
// It should be a fairly straightforward exercise to implement gradual
// underflow with correct rounding.
//--------------------------------------------------------------------------------
fp_t __divsf3(fp_t a, fp_t b) {
    const unsigned int aExponent = toRep(a) >> significandBits & maxExponent;
    const unsigned int bExponent = toRep(b) >> significandBits & maxExponent;
    const rep_t quotientSign = (toRep(a) ^ toRep(b)) & signBit;
    
    rep_t aSignificand = toRep(a) & significandMask;
    rep_t bSignificand = toRep(b) & significandMask;
    int scale = 0;
    
    // Detect if a or b is zero, denormal, infinity, or NaN.
    if (aExponent-1U >= maxExponent-1U || bExponent-1U >= maxExponent-1U) {
        
        const rep_t aAbs = toRep(a) & absMask;
        const rep_t bAbs = toRep(b) & absMask;
        
        // NaN / anything = qNaN
        if (aAbs > infRep) return fromRep(toRep(a) | quietBit);
        // anything / NaN = qNaN
        if (bAbs > infRep) return fromRep(toRep(b) | quietBit);
        
        if (aAbs == infRep) {
            // infinity / infinity = NaN
            if (bAbs == infRep) return fromRep(qnanRep);
            // infinity / anything else = +/- infinity
            else return fromRep(aAbs | quotientSign);
        }
        
        // anything else / infinity = +/- 0
        if (bAbs == infRep) return fromRep(quotientSign);
        
        if (!aAbs) {
            // zero / zero = NaN
            if (!bAbs) return fromRep(qnanRep);
            // zero / anything else = +/- zero
            else return fromRep(quotientSign);
        }
        // anything else / zero = +/- infinity
        if (!bAbs) return fromRep(infRep | quotientSign);
        
        // one or both of a or b is denormal, the other (if applicable) is a
        // normal number.  Renormalize one or both of a and b, and set scale to
        // include the necessary exponent adjustment.
        if (aAbs < implicitBit) scale += normalize(&aSignificand);
        if (bAbs < implicitBit) scale -= normalize(&bSignificand);
    }
    
    // Or in the implicit significand bit.  (If we fell through from the
    // denormal path it was already set by normalize( ), but setting it twice
    // won't hurt anything.)
    aSignificand |= implicitBit;
    bSignificand |= implicitBit;
    int quotientExponent = aExponent - bExponent + scale;
    
    // Align the significand of b as a Q31 fixed-point number in the range
    // [1, 2.0) and get a Q32 approximate reciprocal using a small minimax
    // polynomial approximation: reciprocal = 3/4 + 1/sqrt(2) - b/2.  This
    // is accurate to about 3.5 binary digits.
    uint32_t q31b = bSignificand << 8;
    uint32_t reciprocal = UINT32_C(0x7504f333) - q31b;
    
    // Now refine the reciprocal estimate using a Newton-Raphson iteration:
    //
    //     x1 = x0 * (2 - x0 * b)
    //
    // This doubles the number of correct binary digits in the approximation
    // with each iteration, so after three iterations, we have about 28 binary
    // digits of accuracy.
    uint32_t correction;
    correction = -((uint64_t)reciprocal * q31b >> 32);
    reciprocal = (uint64_t)reciprocal * correction >> 31;
    correction = -((uint64_t)reciprocal * q31b >> 32);
    reciprocal = (uint64_t)reciprocal * correction >> 31;
    correction = -((uint64_t)reciprocal * q31b >> 32);
    reciprocal = (uint64_t)reciprocal * correction >> 31;
    
    // Exhaustive testing shows that the error in reciprocal after three steps
    // is in the interval [-0x1.f58108p-31, 0x1.d0e48cp-29], in line with our
    // expectations.  We bump the reciprocal by a tiny value to force the error
    // to be strictly positive (in the range [0x1.4fdfp-37,0x1.287246p-29], to
    // be specific).  This also causes 1/1 to give a sensible approximation
    // instead of zero (due to overflow).
    reciprocal -= 2;
    
    // The numerical reciprocal is accurate to within 2^-28, lies in the
    // interval [0x1.000000eep-1, 0x1.fffffffcp-1], and is strictly smaller
    // than the true reciprocal of b.  Multiplying a by this reciprocal thus
    // gives a numerical q = a/b in Q24 with the following properties:
    //
    //    1. q < a/b
    //    2. q is in the interval [0x1.000000eep-1, 0x1.fffffffcp0)
    //    3. the error in q is at most 2^-24 + 2^-27 -- the 2^24 term comes
    //       from the fact that we truncate the product, and the 2^27 term
    //       is the error in the reciprocal of b scaled by the maximum
    //       possible value of a.  As a consequence of this error bound,
    //       either q or nextafter(q) is the correctly rounded 
    rep_t quotient = (uint64_t)reciprocal*(aSignificand << 1) >> 32;
    
    // Two cases: quotient is in [0.5, 1.0) or quotient is in [1.0, 2.0).
    // In either case, we are going to compute a residual of the form
    //
    //     r = a - q*b
    //
    // We know from the construction of q that r satisfies:
    //
    //     0 <= r < ulp(q)*b
    // 
    // if r is greater than 1/2 ulp(q)*b, then q rounds up.  Otherwise, we
    // already have the correct result.  The exact halfway case cannot occur.
    // We also take this time to right shift quotient if it falls in the [1,2)
    // range and adjust the exponent accordingly.
    rep_t residual;
    if (quotient < (implicitBit << 1)) {
        residual = (aSignificand << 24) - quotient * bSignificand;
        quotientExponent--;
    } else {
        quotient >>= 1;
        residual = (aSignificand << 23) - quotient * bSignificand;
    }

    const int writtenExponent = quotientExponent + exponentBias;
    
    if (writtenExponent >= maxExponent) {
        // If we have overflowed the exponent, return infinity.
        return fromRep(infRep | quotientSign);
    }
    
    else if (writtenExponent < 1) {
        // Flush denormals to zero.  In the future, it would be nice to add
        // code to round them correctly.
        return fromRep(quotientSign);
    }
    
    else {
        const bool round = (residual << 1) > bSignificand;
        // Clear the implicit bit
        rep_t absResult = quotient & significandMask;
        // Insert the exponent
        absResult |= (rep_t)writtenExponent << significandBits;
        // Round
        absResult += round;
        // Insert the sign and return
        return fromRep(absResult | quotientSign);
    }
}

//--------------------------------------------------------------------------------
// Implements the following soft-fp_t comparison routines:
//   __eqsf2   __gesf2   __unordsf2
//   __lesf2   __gtsf2
//   __ltsf2
//   __nesf2
//
// The semantics of the routines grouped in each column are identical, so there
// is a single implementation for each, and wrappers to provide the other names.
//
// The main routines behave as follows:
//
//   __lesf2(a,b) returns -1 if a < b
//                         0 if a == b
//                         1 if a > b
//                         1 if either a or b is NaN
//
//   __gesf2(a,b) returns -1 if a < b
//                         0 if a == b
//                         1 if a > b
//                        -1 if either a or b is NaN
//
//   __unordsf2(a,b) returns 0 if both a and b are numbers
//                           1 if either a or b is NaN
//
// Note that __lesf2( ) and __gesf2( ) are identical except in their handling of
// NaN values.
//--------------------------------------------------------------------------------
enum LE_RESULT {
    LE_LESS      = -1,
    LE_EQUAL     =  0,
    LE_GREATER   =  1,
    LE_UNORDERED =  1
};

enum LE_RESULT __lesf2(fp_t a, fp_t b) {
    
    const srep_t aInt = toRep(a);
    const srep_t bInt = toRep(b);
    const rep_t aAbs = aInt & absMask;
    const rep_t bAbs = bInt & absMask;
    
    // If either a or b is NaN, they are unordered.
    if (aAbs > infRep || bAbs > infRep) return LE_UNORDERED;
    
    // If a and b are both zeros, they are equal.
    if ((aAbs | bAbs) == 0) return LE_EQUAL;
    
    // If at least one of a and b is positive, we get the same result comparing
    // a and b as signed integers as we would with a fp_ting-point compare.
    if ((aInt & bInt) >= 0) {
        if (aInt < bInt) return LE_LESS;
        else if (aInt == bInt) return LE_EQUAL;
        else return LE_GREATER;
    }
    
    // Otherwise, both are negative, so we need to flip the sense of the
    // comparison to get the correct result.  (This assumes a twos- or ones-
    // complement integer representation; if integers are represented in a
    // sign-magnitude representation, then this flip is incorrect).
    else {
        if (aInt > bInt) return LE_LESS;
        else if (aInt == bInt) return LE_EQUAL;
        else return LE_GREATER;
    }
}

enum GE_RESULT {
    GE_LESS      = -1,
    GE_EQUAL     =  0,
    GE_GREATER   =  1,
    GE_UNORDERED = -1   // Note: different from LE_UNORDERED
};

enum GE_RESULT __gesf2(fp_t a, fp_t b) {
    
    const srep_t aInt = toRep(a);
    const srep_t bInt = toRep(b);
    const rep_t aAbs = aInt & absMask;
    const rep_t bAbs = bInt & absMask;
    
    if (aAbs > infRep || bAbs > infRep) return GE_UNORDERED;
    if ((aAbs | bAbs) == 0) return GE_EQUAL;
    if ((aInt & bInt) >= 0) {
        if (aInt < bInt) return GE_LESS;
        else if (aInt == bInt) return GE_EQUAL;
        else return GE_GREATER;
    } else {
        if (aInt > bInt) return GE_LESS;
        else if (aInt == bInt) return GE_EQUAL;
        else return GE_GREATER;
    }
}

int __unordsf2(fp_t a, fp_t b) {
    const rep_t aAbs = toRep(a) & absMask;
    const rep_t bAbs = toRep(b) & absMask;
    return aAbs > infRep || bAbs > infRep;
}

// The following are alternative names for the preceeding routines.

enum LE_RESULT __eqsf2(fp_t a, fp_t b) {
    return __lesf2(a, b);
}

enum LE_RESULT __ltsf2(fp_t a, fp_t b) {
    return __lesf2(a, b);
}

enum LE_RESULT __nesf2(fp_t a, fp_t b) {
    return __lesf2(a, b);
}

enum GE_RESULT __gtsf2(fp_t a, fp_t b) {
    return __gesf2(a, b);
}

//--------------------------------------------------------------------------------
// Converts a 32-bit float to a 32-bit integer.
// No range checking is performed. The behavior of this conversion is undefined for out of range values in the C standard.
//--------------------------------------------------------------------------------
int __fixsfsi(fp_t a) {
    // Break a into sign, exponent, significand
    const rep_t aRep = toRep(a);
    const rep_t aAbs = aRep & absMask;
    const int sign = aRep & signBit ? -1 : 1;
    const int exponent = (aAbs >> significandBits) - exponentBias;
    const rep_t significand = (aAbs & significandMask) | implicitBit;
    
    // If 0 < exponent < significandBits, right shift to get the result.
    if ((unsigned int)exponent < significandBits) {
        return sign * (significand >> (significandBits - exponent));
    }   
    // If exponent is negative, the result is zero.
    else if (exponent < 0) {
        return 0;
    }   
    // If significandBits < exponent, left shift to get the result.  This shift
    // may end up being larger than the type width, which incurs undefined
    // behavior, but the conversion itself is undefined in that case, so
    // whatever the compiler decides to do is fine.
    else {
        return sign * (significand << (exponent - significandBits));
    }
}

//--------------------------------------------------------------------------------
// Convert a 32-bit float to a 32-bit unsigned integer with rounding toward zero.
// Negative values all become zero.
//--------------------------------------------------------------------------------
su_int __fixunssfsi(float a) {
    float_bits fb;
    fb.f = a;
    int e = ((fb.u & 0x7F800000) >> 23) - 127;
    if (e < 0 || (fb.u & 0x80000000))
        return 0;
    su_int r = (fb.u & 0x007FFFFF) | 0x00800000;
    if (e > 23)
        r <<= (e - 23);
    else
        r >>= (23 - e);
    return r;
}

//--------------------------------------------------------------------------------
// Converts a 32-bit signed integer to a 32-bit float with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
fp_t __floatsisf(int a) {
    const int aWidth = sizeof a * CHAR_BIT;
    
    // Handle zero as a special case to protect clz
    if (a == 0)
        return fromRep(0);
    
    // All other cases begin by extracting the sign and absolute value of a
    rep_t sign = 0;
    if (a < 0) {
        sign = signBit;
        a = -a;
    }
    
    // Exponent of (fp_t)a is the width of abs(a).
    const int exponent = (aWidth - 1) - __builtin_clz(a);
    rep_t result;
    
    // Shift a into the significand field, rounding if it is a right-shift
    if (exponent <= significandBits) {
        const int shift = significandBits - exponent;
        result = (rep_t)a << shift ^ implicitBit;
    } else {
        const int shift = exponent - significandBits;
        result = (rep_t)a >> shift ^ implicitBit;
        rep_t round = (rep_t)a << (typeWidth - shift);
        if (round > signBit) result++;
        if (round == signBit) result += result & 1;
    }
    
    // Insert the exponent
    result += (rep_t)(exponent + exponentBias) << significandBits;
    // Insert the sign bit and return
    return fromRep(result | sign);
}

//--------------------------------------------------------------------------------
// Converts a 32-bit unsigned integer to a 32-bit float with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
fp_t __floatunsisf(unsigned int a) {
    const int aWidth = sizeof a * CHAR_BIT;
    
    // Handle zero as a special case to protect clz
    if (a == 0) return fromRep(0);
    
    // Exponent of (fp_t)a is the width of abs(a).
    const int exponent = (aWidth - 1) - __builtin_clz(a);
    rep_t result;
    
    // Shift a into the significand field, rounding if it is a right-shift
    if (exponent <= significandBits) {
        const int shift = significandBits - exponent;
        result = (rep_t)a << shift ^ implicitBit;
    } else {
        const int shift = exponent - significandBits;
        result = (rep_t)a >> shift ^ implicitBit;
        rep_t round = (rep_t)a << (typeWidth - shift);
        if (round > signBit) result++;
        if (round == signBit) result += result & 1;
    }
    
    // Insert the exponent
    result += (rep_t)(exponent + exponentBias) << significandBits;
    return fromRep(result);
}

//--------------------------------------------------------------------------------
// Converts a 64-bit unsigned integer to a 32-bit float with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
float __floatundisf(du_int a)
{
    if (a == 0)
        return 0.0F;
    const unsigned N = sizeof(du_int) * CHAR_BIT;
    int sd = N - __builtin_clzll(a);  /* number of significant digits */
    int e = sd - 1;             /* 8 exponent */
    if (sd > FLT_MANT_DIG)
    {
        /*  start:  0000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQxxxxxxxxxxxxxxxxxx
         *  finish: 000000000000000000000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQR
         *                                                12345678901234567890123456
         *  1 = msb 1 bit
         *  P = bit FLT_MANT_DIG-1 bits to the right of 1
         *  Q = bit FLT_MANT_DIG bits to the right of 1
         *  R = "or" of all bits to the right of Q
         */
        switch (sd)
        {
        case FLT_MANT_DIG + 1:
            a <<= 1;
            break;
        case FLT_MANT_DIG + 2:
            break;
        default:
            a = (a >> (sd - (FLT_MANT_DIG+2))) |
                ((a & ((du_int)(-1) >> ((N + FLT_MANT_DIG+2) - sd))) != 0);
        }
        /* finish: */
        a |= (a & 4) != 0;  /* Or P into R */
        ++a;  /* round - this step may add a significant bit */
        a >>= 2;  /* dump Q and R */
        /* a is now rounded to FLT_MANT_DIG or FLT_MANT_DIG+1 bits */
        if (a & ((du_int)1 << FLT_MANT_DIG)) {
            a >>= 1;
            ++e;
        }
        /* a is now rounded to FLT_MANT_DIG bits */
    }
    else
    {
        a <<= (FLT_MANT_DIG - sd);
        /* a is now rounded to FLT_MANT_DIG bits */
    }
    float_bits fb;
    fb.u = ((e + 127) << 23)       |  /* exponent */
           ((su_int)a & 0x007FFFFF);  /* mantissa */
    return fb.f;
}
