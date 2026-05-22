#!/bin/sh
cargo asm -p field --lib -C target_feature=+zimop --rust --target=riscv32i-unknown-none-elf --features=modular_fma test_e4_fma_via_fma_option