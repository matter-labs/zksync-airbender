/* Execute-only ROM variant of ../32mb_total_no_heap/memory.x: the 4 MB ROM holds code only and is
   never read as data; .rodata/.data live in RAM from the start (no ROM copy of their
   initial content), see link.x in this folder. */
MEMORY
{
  ROM (x): ORIGIN = 0, LENGTH = 4M
  RAM (rwa!x) : ORIGIN = 4M, LENGTH = 28M
}

REGION_ALIAS("REGION_TEXT", ROM);
REGION_ALIAS("REGION_STACK", RAM);
REGION_ALIAS("REGION_DATA", RAM);
REGION_ALIAS("REGION_RODATA", RAM);
REGION_ALIAS("REGION_BSS", RAM);
REGION_ALIAS("REGION_HEAP", RAM);

PROVIDE(_hart_stack_size = 16M);
PROVIDE(_heap_size = 0);
