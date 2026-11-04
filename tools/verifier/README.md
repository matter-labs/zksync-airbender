# ZK verifier example

This crate verifies RISC-V FRI proofs inside the RISC-V verifier program.

The verifier workloads are compiled as separate artifacts for each proof security, but
security selection is now local to this crate: `src/main.rs` dispatches explicitly into
the migrated `verify_80` / `verify_100` entrypoints instead of relying on dependency-level
security feature gating.

Build the current artifact set with:

```sh
./build.sh
```

To build one artifact manually, pick both a workload feature and a local security selector:

```sh
cargo objcopy --release \
  -Z build-std=core,panic_abort,alloc \
  --no-default-features \
  --features recursion_in_unrolled_layer,security_80 \
  -- -O binary recursion_in_unrolled_layer.bin
```

Use `security_100` to produce the 100-bit variant, and `recursion_in_unified_layer` for the
unified recursion verifier.

Run and prove these binaries on the `mini` machine. The program also uses 2 MB of ROM
from `riscv_common`'s linker script because the verifier image is large.
