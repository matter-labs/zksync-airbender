/* Execute-only-text layout (riscv_common feature `execute_only_text`).

   Differences from the regular scripts (../<ram size>/link.x):
   - the ROM region is execute-only (memory_*.x): the program never reads it as data, so the
     reader side (`riscv_transpiler::elf::ElfReadMode::Strict`) treats every load from the ROM
     range as an error and the VM can enforce it;
   - .rodata and .data have NO load image in ROM: they are placed in RAM with LMA == VMA. Their
     initial content stays in the ELF file as ordinary PROGBITS sections, which nothing loads
     into the (zero-initialised) guest RAM; it is materialised by code instead;
   - that code is spliced into the `init_from_text` stub, which is always the LAST function of
     .text: `_init_from_text` / `_einit_from_text` bracket it (an absolute offset into .text), the
     stub itself is a single `ret`, and the host-side ELF post-processing replaces it by the
     stores that rebuild .rodata/.data followed by `ret` (`ElfImage::init_from_text`). */

PROVIDE(_stext = ORIGIN(REGION_TEXT));
PROVIDE(_rom_size = LENGTH(ROM));
PROVIDE(_max_hart_id = 0);

PROVIDE(__pre_init = default_pre_init);
PROVIDE(_start_trap = default_start_trap);
PROVIDE(_machine_start_trap = machine_default_start_trap);

PHDRS
{
  text PT_LOAD;
  rodata PT_LOAD;
  data PT_LOAD;
  bss PT_LOAD;
}

SECTIONS
{
  .text.dummy (NOLOAD) :
  {
    /* This section is intended to make _stext address work */
    . = ABSOLUTE(_stext);
  } > REGION_TEXT AT > REGION_TEXT :text

  .text _stext : ALIGN(4096)
  {
    /* Put reset handler first in .text section so it ends up as the entry */
    /* point of the program. */
    KEEP(*(.init));
    KEEP(*(.init.rust));
    . = ALIGN(4);
    *(.trap);
    *(.trap.rust);

    *(.text .text.*);

    /* The init_from_text stub is the very last thing in .text so that post-processing can
       find it by `_init_from_text` and grow it (the spliced code extends .text). */
    . = ALIGN(4);
    _init_from_text = .;
    KEEP(*(.init_from_text));
    . = ALIGN(4);
    _einit_from_text = .;
    _etext = .;
  } > REGION_TEXT AT > REGION_TEXT :text

  /* fictitious region that represents the memory available for the stack */
  .stack ORIGIN(REGION_STACK) (NOLOAD) : ALIGN(4096)
  {
    _estack = .;
    . += (_max_hart_id + 1) * _hart_stack_size;
    . = ALIGN(4);
    _sstack = .;
  } > REGION_STACK

  /* No `AT >`: the initial content lives at the run-time address (LMA == VMA, in RAM). */
  .rodata : ALIGN(4)
  {
    _sirodata = LOADADDR(.rodata);
    _srodata = .;
    *(.srodata .srodata.*);
    *(.rodata .rodata.*);
    . = ALIGN(4);
    _erodata = .;
  } > REGION_RODATA :rodata

  .data : ALIGN(4096)
  {
    _sidata = LOADADDR(.data);
    _sdata = .;
    /* Must be called __global_pointer$ for linker relaxations to work. */
    PROVIDE(__global_pointer$ = . + 0x800);
    *(.sdata .sdata.* .sdata2 .sdata2.*);
    *(.data .data.*);
    . = ALIGN(4);
    _edata = .;
  } > REGION_DATA :data

  .bss (NOLOAD) : ALIGN(4096)
  {
    _sbss = .;
    *(.sbss .sbss.* .bss .bss.*);
    . = ALIGN(4);
    _ebss = .;
  } > REGION_BSS AT > REGION_BSS :bss

  /* fictitious region that represents the memory available for the heap */
  .heap (NOLOAD) : ALIGN(2097152)
  {
    _sheap = .;
    . += _heap_size;
    . = ALIGN(2097152);
    _eheap = .;
  } > REGION_HEAP

  /* fake output .got section */
  /* Dynamic relocations are unsupported. This section is only used to detect
     relocatable code in the input files and raise an error if relocatable code
     is found */
  .got (INFO) :
  {
    KEEP(*(.got .got.*));
  }

  .eh_frame (INFO) : { KEEP(*(.eh_frame)) }
  .eh_frame_hdr (INFO) : { *(.eh_frame_hdr) }
}

/* Do not exceed this mark in the error messages above                                    | */
ASSERT(ORIGIN(REGION_TEXT) % 4 == 0, "
ERROR(riscv-rt): the start of the REGION_TEXT must be 4-byte aligned");

ASSERT(ORIGIN(REGION_RODATA) % 4 == 0, "
ERROR(riscv-rt): the start of the REGION_RODATA must be 4-byte aligned");

ASSERT(ORIGIN(REGION_DATA) % 4 == 0, "
ERROR(riscv-rt): the start of the REGION_DATA must be 4-byte aligned");

ASSERT(ORIGIN(REGION_HEAP) % 4 == 0, "
ERROR(riscv-rt): the start of the REGION_HEAP must be 4-byte aligned");

ASSERT(ORIGIN(REGION_STACK) % 4 == 0, "
ERROR(riscv-rt): the start of the REGION_STACK must be 4-byte aligned");

ASSERT(_stext % 4 == 0, "
ERROR(riscv-rt): `_stext` must be 4-byte aligned");

ASSERT(_srodata % 4 == 0 && _erodata % 4 == 0, "
BUG(riscv-rt): .rodata is not 4-byte aligned");

ASSERT(_sdata % 4 == 0 && _edata % 4 == 0, "
BUG(riscv-rt): .data is not 4-byte aligned");

ASSERT(_sbss % 4 == 0 && _ebss % 4 == 0, "
BUG(riscv-rt): .bss is not 4-byte aligned");

ASSERT(_sheap % 4 == 0, "
BUG(riscv-rt): start of .heap is not 4-byte aligned");

ASSERT(_stext + SIZEOF(.text) < ORIGIN(REGION_TEXT) + LENGTH(REGION_TEXT), "
ERROR(riscv-rt): The .text section must be placed inside the REGION_TEXT region.
Set _stext to an address smaller than 'ORIGIN(REGION_TEXT) + LENGTH(REGION_TEXT)'");

ASSERT(_einit_from_text == _stext + SIZEOF(.text), "
ERROR(execute_only_text): the init_from_text stub is not the last function of .text");

ASSERT(_einit_from_text - _init_from_text == 4, "
ERROR(execute_only_text): the init_from_text stub must be a single `ret` (4 bytes);
is riscv_common built with the `execute_only_text` feature?");

ASSERT(_sirodata == _srodata && _sidata == _sdata, "
ERROR(execute_only_text): .rodata/.data must not be relocated (LMA == VMA in RAM)");

ASSERT(SIZEOF(.stack) >= (_max_hart_id + 1) * _hart_stack_size, "
ERROR(riscv-rt): .stack section is too small for allocating stacks for all the harts.
Consider changing `_max_hart_id` or `_hart_stack_size`.");

ASSERT(SIZEOF(.got) == 0, "
.got section detected in the input files. Dynamic relocations are not
supported. If you are linking to C code compiled using the `gcc` crate
then modify your build script to compile the C code _without_ the
-fPIC flag. See the documentation of the `gcc::Config.fpic` method for
details.");

/* Do not exceed this mark in the error messages above                                    | */
