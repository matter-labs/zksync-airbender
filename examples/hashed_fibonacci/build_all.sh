#!/bin/sh
rm app_*.bin
rm app_*.elf
rm app_*.text

cargo build --release  # easier errors
cargo objcopy --release -- -O binary app_plain.bin
cargo objcopy --release -- -R .text app_plain.elf
cargo objcopy --release -- -O binary --only-section=.text app_plain.text

cargo build --release --features=mop_extension # easier errors
cargo objcopy --release --features=mop_extension -- -O binary app_mop_extension.bin
cargo objcopy --release --features=mop_extension -- -R .text app_mop_extension.elf
cargo objcopy --release --features=mop_extension -- -O binary --only-section=.text app_mop_extension.text

cargo build --release --features=blake2_g_function # easier errors
cargo objcopy --release --features=blake2_g_function -- -O binary app_blake2_g_function.bin
cargo objcopy --release --features=blake2_g_function -- -R .text app_blake2_g_function.elf
cargo objcopy --release --features=blake2_g_function -- -O binary --only-section=.text app_blake2_g_function.text

cargo build --release --features=blake2_with_compression # easier errors
cargo objcopy --release --features=blake2_with_compression -- -O binary app_blake2_with_compression.bin
cargo objcopy --release --features=blake2_with_compression -- -R .text app_blake2_with_compression.elf
cargo objcopy --release --features=blake2_with_compression -- -O binary --only-section=.text app_blake2_with_compression.text