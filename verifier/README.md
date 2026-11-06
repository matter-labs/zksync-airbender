### How to use

- compile your circuit and dump to file as in https://github.com/matter-labs/air_compiler/blob/8d357a3756587dfda312dba5efb106e3a3205ea1/prover/src/tests/mod.rs#L410
- use tests in https://github.com/matter-labs/air_compiler/tree/av_one_row_compiler/verifier_generator to generate two files and copy them here
- can run test that reads a proof and simulates feeding the data through CSR register

### Miri CI

The `Miri verifier` workflow checks `verifier_common` unit tests, generated helpers and one full unrolled base-layer FSV verification over the persisted hashed-Fibonacci Sec100 pessimistic proof (reads `[0, 1]`). It covers add/sub, branch, shift, word memory, inits/teardowns and Blake2 delegation. A separate 45-minute high-performance currency job regenerates the compact JSON/zlib proof, setups and manifest and byte-compares them with the committed fixture; the eight-worker producer needs about 58 GiB RSS. The 30-minute Miri job prepares and verifies its static input natively, then embeds it at compile time with default Stacked Borrows, recursive validation and symbolic alignment. Missing input fails compilation. The non-default `miri_fsv` host test feature selects the production Compression guest's opening layout; normal host and RISC-V behavior is unchanged. Current code reports U02 at the FSV's uninitialized register array; no UB workarounds or ignored failures are applied. Regeneration instructions and fixture identity are in [the fixture README](../full_statement_verifier/tests/fixtures/hashed_fibonacci/README.md). From the repository root:

```sh
export RUSTC_WRAPPER= CARGO_BUILD_RUSTC_WRAPPER= CARGO_BUILD_JOBS=4
export CARGO_TARGET_DIR="$PWD/target/miri-fsv/hashed-fibonacci" CARGO_INCREMENTAL=0 CARGO_PROFILE_DEV_DEBUG=0
export RUST_MIN_STACK=134217728 RAYON_NUM_THREADS=8
export MIRIFLAGS="-Zmiri-recursive-validation -Zmiri-symbolic-alignment-check"
export AIRBENDER_MIRI_FSV_INPUT="$CARGO_TARGET_DIR/input.bin"
cargo miri setup
mkdir -p "$CARGO_TARGET_DIR"
cargo run -p full_statement_verifier --no-default-features --features host_utils,miri_fsv --example miri_input -- "$AIRBENDER_MIRI_FSV_INPUT"
export CARGO_NET_OFFLINE=true
cargo miri test -p verifier_common --no-default-features --lib
cargo miri test -p verifier --no-default-features --test generated_common
cargo miri test -p full_statement_verifier --no-default-features --features miri_fsv --test miri_native
```
