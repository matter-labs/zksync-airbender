CC=riscv64-elf-gcc
CFLAGS=-march=rv32im_zicsr -mabi=ilp32 -nostdlib -O0 -nolibc -fno-builtin -ffreestanding -T memmap.ld
OBJCOPY=riscv64-elf-objcopy

.PHONY: clean all hello badread badread2 badwrite

all: hello badread badread2

hello: hello.bin hello.text
badread: badread.bin badread.text
badread2: badread2.bin badread2.text
badwrite: badwrite.bin badwrite.text

%.elf: %.c rt.c start.s uart.c
	${CC} ${CFLAGS} -o $@ $^

%.bin: %.elf 
	${OBJCOPY} -O binary $^ $@ 

%.text: %.elf 
	${OBJCOPY} -O binary --only-section=.text $^ $@ 

%.asm: %.c 
	${CC} ${CFLAGS} -o $@ $^ -S

clean:
	rm -rf *.elf *.bin *.text *.asm
