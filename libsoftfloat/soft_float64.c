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

typedef uint64_t rep_t;
typedef int64_t srep_t;
typedef double fp_t;
#define REP_C(a) UINT64_C(a)
#define significandBits 52

static inline int rep_clz(rep_t a) {
#if defined __LP64__
    return __builtin_clzl(a);
#else
    if (a & REP_C(0xffffffff00000000))
        return __builtin_clz(a >> 32);
    else 
        return 32 + __builtin_clz(a & REP_C(0xffffffff));
#endif
}

si_int __clzdi2(di_int a) {
    dwords x;
    x.all = a;
    const si_int f = -(x.s.high == 0);
    return __builtin_clz((x.s.high & ~f) | (x.s.low & f)) +
           (f & ((si_int)(sizeof(si_int) * CHAR_BIT)));
}

#define loWord(a) (a & 0xffffffffU)
#define hiWord(a) (a >> 32)

// 64x64 -> 128 wide multiply for platforms that don't have such an operation;
// many 64-bit platforms have this operation, but they tend to have hardware
// floating-point, so we don't bother with a special case for them here.
static inline void wideMultiply(rep_t a, rep_t b, rep_t *hi, rep_t *lo) {
    // Each of the component 32x32 -> 64 products
    const uint64_t plolo = loWord(a) * loWord(b);
    const uint64_t plohi = loWord(a) * hiWord(b);
    const uint64_t philo = hiWord(a) * loWord(b);
    const uint64_t phihi = hiWord(a) * hiWord(b);
    // Sum terms that contribute to lo in a way that allows us to get the carry
    const uint64_t r0 = loWord(plolo);
    const uint64_t r1 = hiWord(plolo) + loWord(plohi) + loWord(philo);
    *lo = r0 + (r1 << 32);
    // Sum terms contributing to hi with the carry from lo
    *hi = hiWord(plohi) + hiWord(philo) + hiWord(r1) + phihi;
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
fp_t __negdf2(fp_t a) {
    return fromRep(toRep(a) ^ signBit);
}

//--------------------------------------------------------------------------------
// Add / sub.
//--------------------------------------------------------------------------------
fp_t __adddf3(fp_t a, fp_t b) {
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
fp_t __subdf3(fp_t a, fp_t b) {
    return __adddf3(a, fromRep(toRep(b) ^ signBit));
}

//--------------------------------------------------------------------------------
// Multiplication with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
fp_t __muldf3(fp_t a, fp_t b) {
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
        // Result is denormal before rounding
        //
        // If the result is so small that it just underflows to zero, return
        // a zero of the appropriate sign.  Mathematically there is no need to
        // handle this case separately, but we make it a special case to
        // simplify the shift logic.
        const int shift = 1 - productExponent;
        if (shift >= typeWidth) return fromRep(productSign);
        
        // Otherwise, shift the significand of the result so that the round
        // bit is the high bit of productLo.
        wideRightShiftWithSticky(&productHi, &productLo, shift);
    }
    
    else {
        // Result is normal before rounding; insert the exponent.
        productHi &= significandMask;
        productHi |= (rep_t)productExponent << significandBits;
    }
    
    // Insert the sign of the result:
    productHi |= productSign;
    
    // Final rounding.  The final result may overflow to infinity, or underflow
    // to zero, but those are the correct results in those cases.  We use the
    // default IEEE-754 round-to-nearest, ties-to-even rounding mode.
    if (productLo > signBit) productHi++;
    if (productLo == signBit) productHi += productHi & 1;
    return fromRep(productHi);
}

//--------------------------------------------------------------------------------
// Division to nearest, ties to even.
//
// For simplicity, this implementation currently flushes denormals to zero.
// It should be a fairly straightforward exercise to implement gradual
// underflow with correct rounding.
//--------------------------------------------------------------------------------
fp_t __divdf3(fp_t a, fp_t b) {   
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
    const uint32_t q31b = bSignificand >> 21;
    uint32_t recip32 = UINT32_C(0x7504f333) - q31b;
    
    // Now refine the reciprocal estimate using a Newton-Raphson iteration:
    //
    //     x1 = x0 * (2 - x0 * b)
    //
    // This doubles the number of correct binary digits in the approximation
    // with each iteration, so after three iterations, we have about 28 binary
    // digits of accuracy.
    uint32_t correction32;
    correction32 = -((uint64_t)recip32 * q31b >> 32);
    recip32 = (uint64_t)recip32 * correction32 >> 31;
    correction32 = -((uint64_t)recip32 * q31b >> 32);
    recip32 = (uint64_t)recip32 * correction32 >> 31;
    correction32 = -((uint64_t)recip32 * q31b >> 32);
    recip32 = (uint64_t)recip32 * correction32 >> 31;
    
    // recip32 might have overflowed to exactly zero in the preceeding
    // computation if the high word of b is exactly 1.0.  This would sabotage
    // the full-width final stage of the computation that follows, so we adjust
    // recip32 downward by one bit.
    recip32--;
    
    // We need to perform one more iteration to get us to 56 binary digits;
    // The last iteration needs to happen with extra precision.
    const uint32_t q63blo = bSignificand << 11;
    uint64_t correction, reciprocal;
    correction = -((uint64_t)recip32*q31b + ((uint64_t)recip32*q63blo >> 32));
    uint32_t cHi = correction >> 32;
    uint32_t cLo = correction;
    reciprocal = (uint64_t)recip32*cHi + ((uint64_t)recip32*cLo >> 32);
    
    // We already adjusted the 32-bit estimate, now we need to adjust the final
    // 64-bit reciprocal estimate downward to ensure that it is strictly smaller
    // than the infinitely precise exact reciprocal.  Because the computation
    // of the Newton-Raphson step is truncating at every step, this adjustment
    // is small; most of the work is already done.
    reciprocal -= 2;
    
    // The numerical reciprocal is accurate to within 2^-56, lies in the
    // interval [0.5, 1.0), and is strictly smaller than the true reciprocal
    // of b.  Multiplying a by this reciprocal thus gives a numerical q = a/b
    // in Q53 with the following properties:
    //
    //    1. q < a/b
    //    2. q is in the interval [0.5, 2.0)
    //    3. the error in q is bounded away from 2^-53 (actually, we have a
    //       couple of bits to spare, but this is all we need).
    
    // We need a 64 x 64 multiply high to compute q, which isn't a basic
    // operation in C, so we need to be a little bit fussy.
    rep_t quotient, quotientLo;
    wideMultiply(aSignificand << 2, reciprocal, &quotient, &quotientLo);
    
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
        residual = (aSignificand << 53) - quotient * bSignificand;
        quotientExponent--;
    } else {
        quotient >>= 1;
        residual = (aSignificand << 52) - quotient * bSignificand;
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
        const double result = fromRep(absResult | quotientSign);
        return result;
    }
}

//--------------------------------------------------------------------------------
// Implements the following soft-float comparison routines:
//   __eqdf2   __gedf2   __unorddf2
//   __ledf2   __gtdf2
//   __ltdf2
//   __nedf2
//--------------------------------------------------------------------------------
//
// The semantics of the routines grouped in each column are identical, so there
// is a single implementation for each, and wrappers to provide the other names.
//
// The main routines behave as follows:
//
//   __ledf2(a,b) returns -1 if a < b
//                         0 if a == b
//                         1 if a > b
//                         1 if either a or b is NaN
//
//   __gedf2(a,b) returns -1 if a < b
//                         0 if a == b
//                         1 if a > b
//                        -1 if either a or b is NaN
//
//   __unorddf2(a,b) returns 0 if both a and b are numbers
//                           1 if either a or b is NaN
//
// Note that __ledf2( ) and __gedf2( ) are identical except in their handling of
// NaN values.
enum LE_RESULT {
    LE_LESS      = -1,
    LE_EQUAL     =  0,
    LE_GREATER   =  1,
    LE_UNORDERED =  1
};

enum LE_RESULT __ledf2(fp_t a, fp_t b) {
    
    const srep_t aInt = toRep(a);
    const srep_t bInt = toRep(b);
    const rep_t aAbs = aInt & absMask;
    const rep_t bAbs = bInt & absMask;
    
    // If either a or b is NaN, they are unordered.
    if (aAbs > infRep || bAbs > infRep) return LE_UNORDERED;
    
    // If a and b are both zeros, they are equal.
    if ((aAbs | bAbs) == 0) return LE_EQUAL;
    
    // If at least one of a and b is positive, we get the same result comparing
    // a and b as signed integers as we would with a floating-point compare.
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

enum GE_RESULT __gedf2(fp_t a, fp_t b) {
    
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

int __unorddf2(fp_t a, fp_t b) {
    const rep_t aAbs = toRep(a) & absMask;
    const rep_t bAbs = toRep(b) & absMask;
    return aAbs > infRep || bAbs > infRep;
}

// The following are alternative names for the preceeding routines.

enum LE_RESULT __eqdf2(fp_t a, fp_t b) {
    return __ledf2(a, b);
}

enum LE_RESULT __ltdf2(fp_t a, fp_t b) {
    return __ledf2(a, b);
}

enum LE_RESULT __nedf2(fp_t a, fp_t b) {
    return __ledf2(a, b);
}

enum GE_RESULT __gtdf2(fp_t a, fp_t b) {
    return __gedf2(a, b);
}

//--------------------------------------------------------------------------------
// Converts a 32-bit float to 64-bit float.
//
// This routine can be trivially adapted to support conversions from 
// half-precision or to quad-precision. It does not support types that don't
// use the usual IEEE-754 interchange formats; specifically, some work would be
// needed to adapt it to (for example) the Intel 80-bit format or PowerPC
// double-double format.
//
// Note please, however, that this implementation is only intended to support
// *widening* operations; if you need to convert to a *narrower* floating-point
// type (e.g. double -> float), then this routine will not do what you want it
// to.
//
// It also requires that integer types at least as large as both formats
// are available on the target platform; this may pose a problem when trying
// to add support for quad on some 32-bit systems, for example.  You also may
// run into trouble finding an appropriate CLZ function for wide source types;
// you will likely need to roll your own on some platforms.
//
// Finally, the following assumptions are made:
//
// 1. floating-point types and integer types have the same endianness on the
//    target platform
//
// 2. quiet NaNs, if supported, are indicated by the leading bit of the
//    significand field being set
//--------------------------------------------------------------------------------
typedef float src0_t;
typedef uint32_t src0_rep_t;
#define SRC0_REP_C UINT32_C
static const int src0SigBits = 23;
#define src0_rep_t_clz __builtin_clz

typedef double dst0_t;
typedef uint64_t dst0_rep_t;
#define DST0_REP_C UINT64_C
static const int dst0SigBits = 52;

// End of specialization parameters.  Two helper routines for conversion to and
// from the representation of floating-point data as integer values follow.

static inline src0_rep_t src0ToRep(src0_t x) {
    const union { src0_t f; src0_rep_t i; } rep = {.f = x};
    return rep.i;
}

static inline dst0_t dst0FromRep(dst0_rep_t x) {
    const union { dst0_t f; dst0_rep_t i; } rep = {.i = x};
    return rep.f;
}

// End helper routines.  Conversion implementation follows.

dst0_t __extendsfdf2(src0_t a) {
    
    // Various constants whose values follow from the type parameters.
    // Any reasonable optimizer will fold and propagate all of these.
    const int srcBits = sizeof(src0_t)*CHAR_BIT;
    const int srcExpBits = srcBits - src0SigBits - 1;
    const int srcInfExp = (1 << srcExpBits) - 1;
    const int srcExpBias = srcInfExp >> 1;
    
    const src0_rep_t srcMinNormal = SRC0_REP_C(1) << src0SigBits;
    const src0_rep_t srcInfinity = (src0_rep_t)srcInfExp << src0SigBits;
    const src0_rep_t srcSignMask = SRC0_REP_C(1) << (src0SigBits + srcExpBits);
    const src0_rep_t srcAbsMask = srcSignMask - 1;
    const src0_rep_t srcQNaN = SRC0_REP_C(1) << (src0SigBits - 1);
    const src0_rep_t srcNaNCode = srcQNaN - 1;
    
    const int dstBits = sizeof(dst0_t)*CHAR_BIT;
    const int dstExpBits = dstBits - dst0SigBits - 1;
    const int dstInfExp = (1 << dstExpBits) - 1;
    const int dstExpBias = dstInfExp >> 1;
    
    const dst0_rep_t dstMinNormal = DST0_REP_C(1) << dst0SigBits;
    
    // Break a into a sign and representation of the absolute value
    const src0_rep_t aRep = src0ToRep(a);
    const src0_rep_t aAbs = aRep & srcAbsMask;
    const src0_rep_t sign = aRep & srcSignMask;
    dst0_rep_t absResult;
    
    if (aAbs - srcMinNormal < srcInfinity - srcMinNormal) {
        // a is a normal number.
        // Extend to the destination type by shifting the significand and
        // exponent into the proper position and rebiasing the exponent.
        absResult = (dst0_rep_t)aAbs << (dst0SigBits - src0SigBits);
        absResult += (dst0_rep_t)(dstExpBias - srcExpBias) << dst0SigBits;
    }
    
    else if (aAbs >= srcInfinity) {
        // a is NaN or infinity.
        // Conjure the result by beginning with infinity, then setting the qNaN
        // bit (if needed) and right-aligning the rest of the trailing NaN
        // payload field.
        absResult = (dst0_rep_t)dstInfExp << dst0SigBits;
        absResult |= (dst0_rep_t)(aAbs & srcQNaN) << (dst0SigBits - src0SigBits);
        absResult |= aAbs & srcNaNCode;
    }
    
    else if (aAbs) {
        // a is denormal.
        // renormalize the significand and clear the leading bit, then insert
        // the correct adjusted exponent in the destination type.
        const int scale = src0_rep_t_clz(aAbs) - src0_rep_t_clz(srcMinNormal);
        absResult = (dst0_rep_t)aAbs << (dst0SigBits - src0SigBits + scale);
        absResult ^= dstMinNormal;
        const int resultExponent = dstExpBias - srcExpBias - scale + 1;
        absResult |= (dst0_rep_t)resultExponent << dst0SigBits;
    }

    else {
        // a is zero.
        absResult = 0;
    }
    
    // Apply the signbit to (dst0_t)abs(a).
    const dst0_rep_t result = absResult | (dst0_rep_t)sign << (dstBits - srcBits);
    return dst0FromRep(result);
}

//--------------------------------------------------------------------------------
// 64-bit float to 32-bit float with round-to-nearest, ties-to-even.
//
// This routine can be trivially adapted to support conversions to 
// half-precision or from quad-precision. It does not support types that don't
// use the usual IEEE-754 interchange formats; specifically, some work would be
// needed to adapt it to (for example) the Intel 80-bit format or PowerPC
// double-double format.
//
// Note please, however, that this implementation is only intended to support
// *narrowing* operations; if you need to convert to a *wider* floating-point
// type (e.g. float -> double), then this routine will not do what you want it
// to.
//
// It also requires that integer types at least as large as both formats
// are available on the target platform; this may pose a problem when trying
// to add support for quad on some 32-bit systems, for example.
//
// Finally, the following assumptions are made:
//
// 1. floating-point types and integer types have the same endianness on the
//    target platform
//
// 2. quiet NaNs, if supported, are indicated by the leading bit of the
//    significand field being set
//--------------------------------------------------------------------------------
typedef double src1_t;
typedef uint64_t src1_rep_t;
#define SRC1_REP_C(a) UINT64_C(a)
static const int src1SigBits = 52;

typedef float dst1_t;
typedef uint32_t dst1_rep_t;
#define DST1_REP_C(a) UINT32_C(a)
static const int dst1SigBits = 23;

// End of specialization parameters.  Two helper routines for conversion to and
// from the representation of floating-point data as integer values follow.

static inline src1_rep_t src1ToRep(src1_t x) {
    const union { src1_t f; src1_rep_t i; } rep = {.f = x};
    return rep.i;
}

static inline dst1_t dst1FromRep(dst1_rep_t x) {
    const union { dst1_t f; dst1_rep_t i; } rep = {.i = x};
    return rep.f;
}

dst1_t __truncdfsf2(src1_t a) {
    
    // Various constants whose values follow from the type parameters.
    // Any reasonable optimizer will fold and propagate all of these.
    const int srcBits = sizeof(src1_t)*CHAR_BIT;
    const int srcExpBits = srcBits - src1SigBits - 1;
    const int srcInfExp = (1 << srcExpBits) - 1;
    const int srcExpBias = srcInfExp >> 1;
    
    const src1_rep_t srcMinNormal = SRC1_REP_C(1) << src1SigBits;
    const src1_rep_t significandMask1 = srcMinNormal - 1;
    const src1_rep_t srcInfinity = (src1_rep_t)srcInfExp << src1SigBits;
    const src1_rep_t srcSignMask = SRC1_REP_C(1) << (src1SigBits + srcExpBits);
    const src1_rep_t srcAbsMask = srcSignMask - 1;
    const src1_rep_t roundMask = (SRC1_REP_C(1) << (src1SigBits - dst1SigBits)) - 1;
    const src1_rep_t halfway = SRC1_REP_C(1) << (src1SigBits - dst1SigBits - 1);
    
    const int dstBits = sizeof(dst1_t)*CHAR_BIT;
    const int dstExpBits = dstBits - dst1SigBits - 1;
    const int dstInfExp = (1 << dstExpBits) - 1;
    const int dstExpBias = dstInfExp >> 1;
    
    const int underflowExponent = srcExpBias + 1 - dstExpBias;
    const int overflowExponent = srcExpBias + dstInfExp - dstExpBias;
    const src1_rep_t underflow = (src1_rep_t)underflowExponent << src1SigBits;
    const src1_rep_t overflow = (src1_rep_t)overflowExponent << src1SigBits;
    
    const dst1_rep_t dstQNaN = DST1_REP_C(1) << (dst1SigBits - 1);
    const dst1_rep_t dstNaNCode = dstQNaN - 1;

    // Break a into a sign and representation of the absolute value
    const src1_rep_t aRep = src1ToRep(a);
    const src1_rep_t aAbs = aRep & srcAbsMask;
    const src1_rep_t sign = aRep & srcSignMask;
    dst1_rep_t absResult;
    
    if (aAbs - underflow < aAbs - overflow) {
        // The exponent of a is within the range of normal numbers in the
        // destination format.  We can convert by simply right-shifting with
        // rounding and adjusting the exponent.
        absResult = aAbs >> (src1SigBits - dst1SigBits);
        absResult -= (dst1_rep_t)(srcExpBias - dstExpBias) << dst1SigBits;
        
        const src1_rep_t roundBits = aAbs & roundMask;
        
        // Round to nearest
        if (roundBits > halfway)
            absResult++;
        
        // Ties to even
        else if (roundBits == halfway)
            absResult += absResult & 1;
    }
    
    else if (aAbs > srcInfinity) {
        // a is NaN.
        // Conjure the result by beginning with infinity, setting the qNaN
        // bit and inserting the (truncated) trailing NaN field.
        absResult = (dst1_rep_t)dstInfExp << dst1SigBits;
        absResult |= dstQNaN;
        absResult |= aAbs & dstNaNCode;
    }
    
    else if (aAbs > overflow) {
        // a overflows to infinity.
        absResult = (dst1_rep_t)dstInfExp << dst1SigBits;
    }
    
    else {
        // a underflows on conversion to the destination type or is an exact
        // zero.  The result may be a denormal or zero.  Extract the exponent
        // to get the shift amount for the denormalization.
        const int aExp = aAbs >> src1SigBits;
        const int shift = srcExpBias - dstExpBias - aExp + 1;
        
        const src1_rep_t significand = (aRep & significandMask1) | srcMinNormal;
        
        // Right shift by the denormalization amount with sticky.
        if (shift > src1SigBits) {
            absResult = 0;
        } else {
            const bool sticky = significand << (srcBits - shift);
            src1_rep_t denormalizedSignificand = significand >> shift | sticky;
            absResult = denormalizedSignificand >> (src1SigBits - dst1SigBits);
            const src1_rep_t roundBits = denormalizedSignificand & roundMask;
            // Round to nearest
            if (roundBits > halfway)
                absResult++;
            // Ties to even
            else if (roundBits == halfway)
                absResult += absResult & 1;
        }
    }
    
    // Apply the signbit to (dst1_t)abs(a).
    const dst1_rep_t result = absResult | sign >> (srcBits - dstBits);
    return dst1FromRep(result);
    
}

//--------------------------------------------------------------------------------
// 64-bit float to 32-bit signed integer.
// No range checking is performed. The behavior of this conversion is undefined for out of range values in the C standard.
//--------------------------------------------------------------------------------
int __fixdfsi(fp_t a) {
    
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
// Convert a to a unsigned int, rounding toward zero. Negative values all become zero.
//--------------------------------------------------------------------------------
su_int __fixunsdfsi(double a)
{
    double_bits fb;
    fb.f = a;
    int e = ((fb.u.s.high & 0x7FF00000) >> 20) - 1023;
    if (e < 0 || (fb.u.s.high & 0x80000000))
        return 0;
    return (
                0x80000000u                      |
                ((fb.u.s.high & 0x000FFFFF) << 11) |
                (fb.u.s.low >> 21)
           ) >> (31 - e);
}

//--------------------------------------------------------------------------------
// Convert a to a unsigned long long, rounding toward zero. Negative values all become zero.
//--------------------------------------------------------------------------------
du_int __fixunsdfdi(double a)
{
    double_bits fb;
    fb.f = a;
    int e = ((fb.u.s.high & 0x7FF00000) >> 20) - 1023;
    if (e < 0 || (fb.u.s.high & 0x80000000))
        return 0;
    udwords r;
    r.s.high = (fb.u.s.high & 0x000FFFFF) | 0x00100000;
    r.s.low = fb.u.s.low;
    if (e > 52)
        r.all <<= (e - 52);
    else
        r.all >>= (52 - e);
    return r.all;
}

//--------------------------------------------------------------------------------
// Convert a to an unsigned integer, rounding toward zero. Negative values all become zero. 
//--------------------------------------------------------------------------------
du_int __fixunssfdi(float a) {
    if (a <= 0.0f) return 0;
    double da = a;
    su_int high = da / 4294967296.f;               /* da / 0x1p32f; */
    su_int low = da - (double)high * 4294967296.f; /* high * 0x1p32f; */
    return ((du_int)high << 32) | low;
}

//--------------------------------------------------------------------------------
// This file implements integer to double-precision conversion with round-to-nearest, ties-to-even.
//--------------------------------------------------------------------------------
fp_t __floatsidf(int a) {
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
    
    // Shift a into the significand field and clear the implicit bit.  Extra
    // cast to unsigned int is necessary to get the correct behavior for
    // the input INT_MIN.
    const int shift = significandBits - exponent;
    result = (rep_t)(unsigned int)a << shift ^ implicitBit;
    
    // Insert the exponent
    result += (rep_t)(exponent + exponentBias) << significandBits;
    // Insert the sign bit and return
    return fromRep(result | sign);
}

//--------------------------------------------------------------------------------
// Convert an unsigned 64-bit integer to a double, rounding toward even.
//--------------------------------------------------------------------------------
#ifndef __SOFT_FP__
/* Support for systems that have hardware floating-point; we'll set the inexact flag
 * as a side-effect of this computation.
 */

double __floatundidf(du_int a)
{
	static const double twop52 = 0x1.0p52;
	static const double twop84 = 0x1.0p84;
	static const double twop84_plus_twop52 = 0x1.00000001p84;
	
	union { uint64_t x; double d; } high = { .d = twop84 };
	union { uint64_t x; double d; } low = { .d = twop52 };
	
	high.x |= a >> 32;
	low.x |= a & UINT64_C(0x00000000ffffffff);
	
	const double result = (high.d - twop84_plus_twop52) + low.d;
	return result;
}

#else
/* Support for systems that don't have hardware floating-point; there are no flags to
 * set, and we don't want to code-gen to an unknown soft-float implementation.
 */ 

double __floatundidf(du_int a)
{
    if (a == 0)
        return 0.0;
    const unsigned N = sizeof(du_int) * CHAR_BIT;
    int sd = N - __builtin_clzll(a);  /* number of significant digits */
    int e = sd - 1;             /* exponent */
    if (sd > DBL_MANT_DIG)
    {
        /*  start:  0000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQxxxxxxxxxxxxxxxxxx
         *  finish: 000000000000000000000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQR
         *                                                12345678901234567890123456
         *  1 = msb 1 bit
         *  P = bit DBL_MANT_DIG-1 bits to the right of 1
         *  Q = bit DBL_MANT_DIG bits to the right of 1
         *  R = "or" of all bits to the right of Q
         */
        switch (sd)
        {
        case DBL_MANT_DIG + 1:
            a <<= 1;
            break;
        case DBL_MANT_DIG + 2:
            break;
        default:
            a = (a >> (sd - (DBL_MANT_DIG+2))) |
                ((a & ((du_int)(-1) >> ((N + DBL_MANT_DIG+2) - sd))) != 0);
        };
        /* finish: */
        a |= (a & 4) != 0;  /* Or P into R */
        ++a;  /* round - this step may add a significant bit */
        a >>= 2;  /* dump Q and R */
        /* a is now rounded to DBL_MANT_DIG or DBL_MANT_DIG+1 bits */
        if (a & ((du_int)1 << DBL_MANT_DIG))
        {
            a >>= 1;
            ++e;
        }
        /* a is now rounded to DBL_MANT_DIG bits */
    }
    else
    {
        a <<= (DBL_MANT_DIG - sd);
        /* a is now rounded to DBL_MANT_DIG bits */
    }
    double_bits fb;
    fb.u.high = ((e + 1023) << 20)      |        /* exponent */
                ((su_int)(a >> 32) & 0x000FFFFF); /* mantissa-high */
    fb.u.low = (su_int)a;                         /* mantissa-low  */
    return fb.f;
}
#endif

//--------------------------------------------------------------------------------
// Converts an unsigned 32-bit integer to double-precision with round-to-nearest, ties-to-even mode.
//--------------------------------------------------------------------------------
fp_t __floatunsidf(unsigned int a) {
    const int aWidth = sizeof a * CHAR_BIT;
    
    // Handle zero as a special case to protect clz
    if (a == 0) return fromRep(0);
    
    // Exponent of (fp_t)a is the width of abs(a).
    const int exponent = (aWidth - 1) - __builtin_clz(a);
    rep_t result;
    
    // Shift a into the significand field and clear the implicit bit.
    const int shift = significandBits - exponent;
    result = (rep_t)a << shift ^ implicitBit;
    
    // Insert the exponent
    result += (rep_t)(exponent + exponentBias) << significandBits;
    return fromRep(result);
}

//--------------------------------------------------------------------------------
// convert a to a double, rounding toward even
//--------------------------------------------------------------------------------
#ifndef __SOFT_FP__
/* Support for systems that have hardware floating-point; we'll set the inexact flag
 * as a side-effect of this computation.
 */
double __floatdidf(di_int a) {
    static const double twop52 = 4503599627370496.0; // 0x1.0p52
    static const double twop32 = 4294967296.0; // 0x1.0p32
    union { int64_t x; double d; } low = { .d = twop52 };
    const double high = (int32_t)(a >> 32) * twop32;
    low.x |= a & INT64_C(0x00000000ffffffff);
    const double result = (high - twop52) + low.d;
    return result;
}
#else
/* Support for systems that don't have hardware floating-point; there are no flags to
 * set, and we don't want to code-gen to an unknown soft-float implementation.
 */
double __floatdidf(di_int a) {
    if (a == 0)
        return 0.0;
    const unsigned N = sizeof(di_int) * CHAR_BIT;
    const di_int s = a >> (N-1);
    a = (a ^ s) - s;
    int sd = N - __builtin_clzll(a);  /* number of significant digits */
    int e = sd - 1;             /* exponent */
    if (sd > DBL_MANT_DIG) {
        /*  start:  0000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQxxxxxxxxxxxxxxxxxx
         *  finish: 000000000000000000000000000000000000001xxxxxxxxxxxxxxxxxxxxxxPQR
         *                                                12345678901234567890123456
         *  1 = msb 1 bit
         *  P = bit DBL_MANT_DIG-1 bits to the right of 1
         * Q = bit DBL_MANT_DIG bits to the right of 1
         *  R = "or" of all bits to the right of Q
        */
        switch (sd)
        {
        case DBL_MANT_DIG + 1:
            a <<= 1;
            break;
        case DBL_MANT_DIG + 2:
            break;
        default:
            a = ((du_int)a >> (sd - (DBL_MANT_DIG+2))) |
                ((a & ((du_int)(-1) >> ((N + DBL_MANT_DIG+2) - sd))) != 0);
        };
        /* finish: */
        a |= (a & 4) != 0;  /* Or P into R */
        ++a;  /* round - this step may add a significant bit */
        a >>= 2;  /* dump Q and R */
        /* a is now rounded to DBL_MANT_DIG or DBL_MANT_DIG+1 bits */
        if (a & ((du_int)1 << DBL_MANT_DIG))
        {
            a >>= 1;
            ++e;
        }
        /* a is now rounded to DBL_MANT_DIG bits */
    }
    else
    {
        a <<= (DBL_MANT_DIG - sd);
        /* a is now rounded to DBL_MANT_DIG bits */
    }
    double_bits fb;
    fb.u.s.high = ((su_int)s & 0x80000000) |        /* sign */
                  ((e + 1023) << 20)       |        /* exponent */
                  ((su_int)(a >> 32) & 0x000FFFFF); /* mantissa-high */
    fb.u.s.low = (su_int)a;                         /* mantissa-low */
    return fb.f;
}
#endif

//--------------------------------------------------------------------------------
// convert a to a float, rounding toward even.
//------------------------------------------------------------------------------
float __floatdisf(di_int a) {
    if (a == 0)
        return 0.0F;
    const unsigned N = sizeof(di_int) * CHAR_BIT;
    const di_int s = a >> (N-1);
    a = (a ^ s) - s;
    int sd = N - __builtin_clzll(a);  /* number of significant digits */
    int e = sd - 1;             /* exponent */
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
            a = ((du_int)a >> (sd - (FLT_MANT_DIG+2))) |
                ((a & ((du_int)(-1) >> ((N + FLT_MANT_DIG+2) - sd))) != 0);
        };
        /* finish: */
        a |= (a & 4) != 0;  /* Or P into R */
        ++a;  /* round - this step may add a significant bit */
        a >>= 2;  /* dump Q and R */
        /* a is now rounded to FLT_MANT_DIG or FLT_MANT_DIG+1 bits */
        if (a & ((du_int)1 << FLT_MANT_DIG))
        {
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
    fb.u = ((su_int)s & 0x80000000) |  /* sign */
           ((e + 127) << 23)       |  /* exponent */
           ((su_int)a & 0x007FFFFF);   /* mantissa */
    return fb.f;
}

//--------------------------------------------------------------------------------
// convert a to a signed integer, rounding toward zero
//-------------------------------------------------------------------------------- 
di_int __fixdfdi(double a) {
    if (a < 0.0) {
        return -__fixunsdfdi(-a);
    }
    return __fixunsdfdi(a);
}

//--------------------------------------------------------------------------------
// convert a to a signed integer, rounding toward zero
//--------------------------------------------------------------------------------
di_int __fixsfdi(float a) {
    if (a < 0.0f) {
        return -__fixunssfdi(-a);
    }
    return __fixunssfdi(a);
}

