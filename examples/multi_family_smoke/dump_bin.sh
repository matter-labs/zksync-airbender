#!/bin/sh
set -e

rm -f app_blake2_g_function.bin app_blake2_g_function.elf app_blake2_g_function.text
rm -f app_blake2_with_compression.bin app_blake2_with_compression.elf app_blake2_with_compression.text
rm -f app.bin app.elf app.text

cargo build --release --features=blake2_g_function
cargo objcopy --release --features=blake2_g_function -- -O binary app_blake2_g_function.bin
cargo objcopy --release --features=blake2_g_function -- -R .text app_blake2_g_function.elf
cargo objcopy --release --features=blake2_g_function -- -O binary --only-section=.text app_blake2_g_function.text

cargo build --release --features=blake2_with_compression
cargo objcopy --release --features=blake2_with_compression -- -O binary app_blake2_with_compression.bin
cargo objcopy --release --features=blake2_with_compression -- -R .text app_blake2_with_compression.elf
cargo objcopy --release --features=blake2_with_compression -- -O binary --only-section=.text app_blake2_with_compression.text
