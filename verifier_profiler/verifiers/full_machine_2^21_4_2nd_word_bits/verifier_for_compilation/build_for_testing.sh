#!/bin/sh
rm tester.bin
rm tester.elf
rm tester.text

cargo build --profile release_with_symbols --features panic_output --no-default-features # easier errors
cargo objcopy --profile release_with_symbols --features panic_output --no-default-features -- -O binary tester.bin
cargo objcopy --profile release_with_symbols --features panic_output --no-default-features -- -R .text tester.elf
cargo objcopy --profile release_with_symbols --features panic_output --no-default-features -- -O binary --only-section=.text tester.text
