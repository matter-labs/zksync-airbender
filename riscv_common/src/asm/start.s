/*
    Entry point of all programs (_start).

    It initializes DWARF call frame information, the stack pointer, the
    frame pointer (needed for closures to work in start_rust) and the global
    pointer. Then it calls _start_rust.
*/

.section .init, "ax"
.global _start

_start:
    /* Jump to the absolute address defined by the linker script. */
    // for 32bit
    # lui ra, %hi(_abs_start)
    # jr %lo(_abs_start)(ra)

    la ra, _abs_start
    jr ra

_abs_start:
    .cfi_startproc
    .cfi_undefined ra
    
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop

    // Assume single core, and put SP to the very top address of the stack region
    la sp, _sstack

    // Set frame pointer
    add s0, sp, zero

    jal zero, _start_rust

    .cfi_endproc

/*
    Machine trap entry point (_machine_start_trap)
*/
.section .trap, "ax"
.global machine_default_start_trap
.align 4
machine_default_start_trap:
    // Stub only
    unimp

/* Make sure there is an abort when linking */
.section .text.abort
.global abort
abort:
    j abort
