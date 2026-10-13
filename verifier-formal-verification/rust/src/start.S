/* Entry point, as zksync-airbender/examples/scripts/asm/asm_reduced.S minus the trap handler. */
.section .init, "ax"
.global _start
_start:
    la ra, _abs_start
    jr ra
_abs_start:
    .option push
    .option norelax
    la gp, __global_pointer$
    .option pop
    la sp, _sstack
    add s0, sp, zero
    jal zero, _start_rust

/* The program has finished (result in a0): Airbender stops when the PC no longer changes. */
.section .text.halt, "ax"
.global _halt
_halt:
    j _halt
