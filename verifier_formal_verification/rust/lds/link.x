/* Trimmed copy of zksync-airbender/examples/scripts/lds/link.x:
   ROM at 0 (.init first, then .text, .rodata); stack at start of RAM; no .data. */
PROVIDE(_stext = ORIGIN(REGION_TEXT));
PROVIDE(_hart_stack_size = 64M);

SECTIONS
{
  .text _stext :
  {
    KEEP(*(.init));
    KEEP(*(.init.rust));
    . = ALIGN(4);
    *(.text .text.*);
  } > REGION_TEXT

  .rodata : ALIGN(4)
  {
    *(.srodata .srodata.*);
    *(.rodata .rodata.*);
    . = ALIGN(4);
  } > REGION_RODATA

  .stack ORIGIN(REGION_STACK) (NOLOAD) : ALIGN(4096)
  {
    _estack = .;
    . += _hart_stack_size;
    . = ALIGN(4);
    _sstack = .;
  } > REGION_STACK

  .data (NOLOAD) : ALIGN(4096)
  {
    PROVIDE(__global_pointer$ = . + 0x800);
    *(.sdata .sdata.* .sdata2 .sdata2.* .data .data.*);
  } > REGION_DATA

  .bss (NOLOAD) : ALIGN(4096)
  {
    *(.sbss .sbss.* .bss .bss.*);
  } > REGION_BSS

  .got (INFO) : { KEEP(*(.got .got.*)); }
  .eh_frame (INFO) : { KEEP(*(.eh_frame)) }
  .eh_frame_hdr (INFO) : { *(.eh_frame_hdr) }
}

ASSERT(SIZEOF(.got) == 0, "dynamic relocations are not supported");
ASSERT(SIZEOF(.data) == 0, ".data must be empty (RAM is zero-initialised)");
