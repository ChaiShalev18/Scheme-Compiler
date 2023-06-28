# makefile
# Used for building executables from 64-bit x86 assembly language
#
# Programmer: Mayer Goldberg, 2022

NASM_EXE = nasm
NASM_OPTIONS = -g
NASM_OPTIONS_64 = -f elf64
NASM_COMMAND_64 = $(NASM_EXE) $(NASM_OPTIONS) $(NASM_OPTIONS_64) \
                  -l $*.lst $<
GCC_EXE = gcc
GCC_OPTIONS = -g
GCC_OPTIONS_64 = -m64 -no-pie
GCC_COMMAND_64 = $(GCC_EXE) $(GCC_OPTIONS) $(GCC_OPTIONS_64) -o $* $*.o

.SUFFIXES:	.asm .o .s
%.o:	%.asm
	$(NASM_COMMAND_64)

%:	%.o
	$(GCC_COMMAND_64)

# end of input
