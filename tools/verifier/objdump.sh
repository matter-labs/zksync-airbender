#!/bin/sh

cargo objdump --release -Z build-std=core,alloc --features unrolled_base_layer,security_80,panic_output --no-default-features -v -- -d
# cargo objdump --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features recursion_step --no-default-features -v -- -d
# cargo objdump --profile cli -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  --features recursion_step --no-default-features -v -- -d
# cargo objdump --profile cli  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort -v -- -d

# cargo objcopy --profile cli  -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort  -- -O binary app.bin
# cargo objdump --features proving --release --target riscv32i-unknown-none-elf -v -- -d