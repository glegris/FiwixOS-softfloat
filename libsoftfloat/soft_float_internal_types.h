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
#ifndef SF_C_InternalTypes_h
#define SF_C_InternalTypes_h

#define LOCAL_LITTLE_ENDIAN

typedef int si_int;
typedef unsigned su_int;

typedef long long di_int;
typedef unsigned long long du_int;

typedef union
{
    di_int all;
    struct
    {
#if defined(LOCAL_LITTLE_ENDIAN)
        su_int low;
        si_int high;
#else
        si_int high;
        su_int low;
#endif
    }s;
} dwords;

typedef union
{
    du_int all;
    struct
    {
#if defined(LOCAL_LITTLE_ENDIAN)
        su_int low;
        su_int high;
#else
        su_int high;
        su_int low;
#endif
    }s;
} udwords;

typedef union
{
    su_int u;
    float f;
} float_bits;

typedef union
{
    udwords u;
    double  f;
} double_bits;

typedef struct
{
#if defined(LOCAL_LITTLE_ENDIAN)
    udwords low;
    udwords high;
#else
    udwords high;
    udwords low;
#endif
} uqwords;

typedef union
{
    uqwords     u;
    long double f;
} long_double_bits;

#endif
