gcc -O2 -ffreestanding -fno-builtin -msoft-float -mno-80387 -mno-mmx -mno-sse -mno-sse2 -march=i386 -m32 -c soft_float32.c -o soft_float32.o
gcc -O2 -ffreestanding -fno-builtin -msoft-float -mno-80387 -mno-mmx -mno-sse -mno-sse2 -march=i386 -m32 -c soft_float64.c -o soft_float64.o
gcc -O2 -ffreestanding -fno-builtin -msoft-float -mno-80387 -mno-fp-ret-in-387 -mno-mmx -mno-sse -mno-sse2 -march=i386 -m32 -c soft_float80.c -o soft_float80.o
ar rc libsoftfloat.a soft_float32.o soft_float64.o  soft_float80.o
ranlib libsoftfloat.a
objcopy --weaken libsoftfloat.a
#cp libsoftfloat.a /usr/i386-pc-fiwix/lib
