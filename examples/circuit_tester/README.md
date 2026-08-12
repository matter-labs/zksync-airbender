# ZK prover example

Simple fibonacci with some extra code to test sensitive circuit parts

Does not use any Oracles (inputs, outputs).

## Building

one time setup:

```
rustup target add riscv32i-unknown-none-elf
rustup component add llvm-tools-preview
```

After each change:
```
cargo build
cargo objcopy  -- -O binary app.bin
```

## Proving
Please use `tools/cli` binary.