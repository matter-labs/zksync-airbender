# Keccak delegation example

This example runs a small Keccak-f1600 sanity suite on RISC-V.

The program compares the unified `common_constants::keccak_f1600` delegation API
against a local software Keccak-f1600 implementation and a known permutation
test vector. Any mismatch triggers the standard guest panic path.

## Rebuilding

If you change the example source, rebuild the binary artifacts by running
`dump_bin.sh`.
