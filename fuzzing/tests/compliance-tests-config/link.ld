OUTPUT_ARCH( "riscv" )
ENTRY(rvtest_entry_point)

/* SECTIONS */
/* { */
/*   . = 0x00000000; */
/*   .text : { *(.text.init) *(.text) } */
/*   . = ALIGN(0x40000); */
/*   .bss : { *(.bss) } */
/*   . = ALIGN(0x10000); */
/*   .data : { *(.data) } */
/*   . = ALIGN(0x10000); */
/*   _end = .; */
/* } */

STACK_SIZE = 0x100000; /* 1 MB */
ROM_SIZE = 0x400000; /* 4 MB */

SECTIONS
{
    .text  0x00000000      :  { *(.text.init) *(.text*) }
    __text_end             = .;
    .rodata                :  { *(.rodata*) *(.srodata*) }
    .data /* ALIGN(ROM_SIZE) */ :  { *(.sdata*) }
    __bss_start            = ROM_SIZE;
    .bss 0x00400000 (NOLOAD) :  { *(.bss*)  *(.sbss*) *(COMMON) }
    __bss_end              = .;
    .heap  0x04000000      :  { __heap_start = .; }
    .stack 0x10000000 - STACK_SIZE : {
        __heap_max = .;
        . = . + STACK_SIZE;
        __stack_top = .;
    }
    __elf_start = .;
}

ASSERT(ADDR(.bss) >= ROM_SIZE, ".bss must be outside ROM")
ASSERT(rvtest_entry_point == ADDR(.text),  /* error if _start not at correct address */
       "rvtest_entry_point symbol must be placed first in text section")
