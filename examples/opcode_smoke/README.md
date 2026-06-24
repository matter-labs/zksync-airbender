# Opcode smoke example

This example stitches together one small self-check for each RV32IM opcode path
currently supported by the full unsigned proving flow, plus `CSRRW` through the
non-determinism CSR.

It is intended to back the CPU/GPU smoke prove+verify matrix, not to replace
the more granular circuit-level compliance tests.

`input.txt` contains the single non-determinism word consumed by the `CSRRW`
check.

If you change `src/main.rs`, regenerate `app.bin`, `app.text`, and `app.elf`
with `dump_bin.sh`.
