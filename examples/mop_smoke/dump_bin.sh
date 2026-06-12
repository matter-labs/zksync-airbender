#!/bin/sh
rm app.bin
rm app.elf
rm app.text

cargo build --release -Z build-std=core,alloc # easier errors
cargo objcopy --release -Z build-std=core,alloc -- -O binary app.bin
cargo objcopy --release -Z build-std=core,alloc -- -R .text app.elf
cargo objcopy --release -Z build-std=core,alloc -- -O binary --only-section=.text app.text