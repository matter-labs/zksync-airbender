
.attribute arch, "rv32im"

# Identify this section to linker script memmap.ld
.section ".text.start"

.type _start, @function
.global _start
.global __stack_top


_start:
  la ra, _abs_start
  jr ra

_abs_start:
  .cfi_startproc
  .cfi_undefined ra           

  # .option push
  # .option norelax
  # la gp, __global_pointer$
  # .option pop

  la sp, __stack_top 

  add s0, sp, zero

  jal zero, _start_c
  
  .cfi_endproc
