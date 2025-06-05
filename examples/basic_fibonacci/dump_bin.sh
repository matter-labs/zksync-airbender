#!/bin/sh
rm app.bin
rm app.elf
rm app.text

cargo build --release # easier errors
cargo objcopy --release -- -O binary app.bin
cargo objcopy --release -- -R .text app.elf
cargo objcopy --release -- -O binary --only-section=.text app.text