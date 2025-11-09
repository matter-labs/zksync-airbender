#!/bin/sh
rm tester.bin
rm tester.elf
rm tester.text

# cargo build --profile release_with_symbols --features verifier_tests,panic_output --no-default-features # easier errors
# cargo objcopy --profile release_with_symbols --features verifier_tests,panic_output --no-default-features -- -O binary tester.bin
# cargo objcopy --profile release_with_symbols --features verifier_tests,panic_output --no-default-features -- -R .text tester.elf
# cargo objcopy --profile release_with_symbols --features verifier_tests,panic_output --no-default-features -- -O binary --only-section=.text tester.text

# cargo build --release --features unrolled_base_layer,security_80,panic_output --no-default-features # easier errors
cargo bloat --release --features unrolled_base_layer,security_80,panic_output --no-default-features -n 32 
# cargo bloat --profile cli --features unrolled_base_layer,security_80,panic_output --no-default-features -n 10 # easier errors
# cargo bloat --profile release_with_symbols --features unrolled_base_layer,security_80,panic_output --no-default-features -n 10 # easier errors
# cargo build --profile release_with_symbols --features unrolled_base_layer,security_80,panic_output --no-default-features # easier errors
# cargo objcopy --profile release_with_symbols --features unrolled_base_layer,security_80,panic_output --no-default-features -- -O binary tester.bin
# cargo objcopy --profile release_with_symbols --features unrolled_base_layer,security_80,panic_output --no-default-features -- -R .text tester.elf
# cargo objcopy --profile release_with_symbols --features unrolled_base_layer,security_80,panic_output --no-default-features -- -O binary --only-section=.text tester.text
