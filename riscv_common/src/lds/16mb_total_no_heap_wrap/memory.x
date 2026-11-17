MEMORY
{
  ROM (rx): ORIGIN = 0, LENGTH = 512K
  RAM (rwa!x) : ORIGIN = 512K, LENGTH = 15872K
}

REGION_ALIAS("REGION_TEXT", ROM);
REGION_ALIAS("REGION_DATAINIT", ROM);
REGION_ALIAS("REGION_RODATAINIT", ROM);
REGION_ALIAS("REGION_STACK", RAM);
REGION_ALIAS("REGION_DATA", RAM);
REGION_ALIAS("REGION_RODATA", RAM);
REGION_ALIAS("REGION_BSS", RAM);
REGION_ALIAS("REGION_HEAP", RAM);

/* Override the shared script default before it is read. */
PROVIDE(_hart_stack_size = 8M);

/* The wrap guest uses a 512 KiB image and 16 MiB address space. */
ASSERT(_rom_size == 0x80000 && _estack == _rom_size,
       "wrap ROM and stack boundary must be 512 KiB");
ASSERT(_sstack == 0x880000, "wrap stack reservation must be 8 MiB");
ASSERT(LOADADDR(.text) + SIZEOF(.text) <= ORIGIN(ROM) + LENGTH(ROM),
       "wrap text LMA exceeds ROM");
ASSERT(LOADADDR(.rodata) + SIZEOF(.rodata) <= ORIGIN(ROM) + LENGTH(ROM),
       "wrap rodata LMA exceeds ROM");
ASSERT(LOADADDR(.data) + SIZEOF(.data) <= ORIGIN(ROM) + LENGTH(ROM),
       "wrap data LMA exceeds ROM");
ASSERT(_srodata >= _sstack && _erodata <= ORIGIN(RAM) + LENGTH(RAM),
       "wrap rodata VMA exceeds RAM or overlaps stack");
ASSERT(_sdata >= _sstack && _edata <= ORIGIN(RAM) + LENGTH(RAM),
       "wrap data VMA exceeds RAM or overlaps stack");
ASSERT(_sbss >= _sstack && _ebss <= ORIGIN(RAM) + LENGTH(RAM),
       "wrap bss VMA exceeds RAM or overlaps stack");
ASSERT(_heap_size == 0 && _sheap == _eheap && _eheap <= ORIGIN(RAM) + LENGTH(RAM),
       "wrap guest has no heap");
