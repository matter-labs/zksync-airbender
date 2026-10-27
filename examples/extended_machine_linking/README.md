# extended_machine_linking

`circuit_tester` rebuilt for the execute-only-text layout of `riscv_common` (feature
`execute_only_text`): the 4 MB ROM holds code only and is never read as data, `.rodata` and
`.data` start in RAM (their initial content stays in the ELF but is not loaded into the guest),
and the `init_from_text` stub at the very end of `.text` is replaced by the host-side ELF
post-processing (`riscv_transpiler::elf::ElfReadMode::Strict`) with the code that materialises
those sections. The program makes both sections non-empty and uses byte/halfword accesses and
`mul`/`mulhu`, so it needs the unified extended machine
(`cs::gkr_circuits::unified_extended_machine`), which proves it in
`prover/src/tests/gkr/unified_extended_circuit.rs`.

## Building

```
rustup +1.99.1 target add riscv32i-unknown-none-elf
rustup +1.99.1 component add llvm-tools
./dump_bin.sh
```

Only `app.elf` is committed; there is no `app.bin`/`app.text` (see `dump_bin.sh`).
