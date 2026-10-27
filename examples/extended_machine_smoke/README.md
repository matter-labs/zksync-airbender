# extended_machine_smoke

Hand-assembled RISC-V words (no toolchain) exercising every sub-word load/store variant
(`lb`/`lbu`/`lh`/`lhu`/`sb`/`sh`) at every byte offset, negative immediates, and
`mul`/`mulhu` on edge operands. Used by the single-cycle tests of the unified extended machine
(`prover/src/tests/single_cycle_tests/unified_extended_circuit_tests.rs`).

`app.bin` and `app.text` are identical (no data sections). Regenerate with
`python3 assemble.py`.
