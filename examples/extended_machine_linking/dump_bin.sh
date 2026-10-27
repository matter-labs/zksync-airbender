#!/bin/sh
# Execute-only-text program: only the ELF is kept. There is no flat ROM image (`objcopy -O
# binary` would include the .rodata/.data images that live in RAM) and the .text the VM runs is
# produced by the host-side post-processing of the ELF (`ElfReadMode::Strict`), not by objcopy.
set -e
rm -f app.elf

# Stable 1.99.1 ships the riscv32i target; RUSTC_BOOTSTRAP unlocks the `field` crate's
# riscv-only `core_intrinsics` feature (as tools/gkr_verifier does), so no nightly is needed.
RUSTC_BOOTSTRAP=1 cargo +1.99.1 build --release
cp target/riscv32i-unknown-none-elf/release/extended_machine_linking app.elf
