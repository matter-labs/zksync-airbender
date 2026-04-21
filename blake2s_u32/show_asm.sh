#!/bin/sh
cargo asm -p blake2s_u32 --lib -C target_feature=+zimop --rust --target=riscv32i-unknown-none-elf --features=mop_extension blake2s_u32::mixing_function