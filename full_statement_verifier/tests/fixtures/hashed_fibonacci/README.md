# Hashed Fibonacci Miri fixture

This is an unrolled base-layer Sec100 pessimistic-conjecture ProgramProof and its six program setups for the committed `examples/hashed_fibonacci/app_blake2_with_compression` binary. CSR reads `[0, 1]` request zero Fibonacci iterations and one full-round hash, producing ten Blake2 round delegation calls. It contains one proof each for add/sub, branch, shift, word memory, inits/teardowns and Blake2 compression. The manifest records decoded program identity, counts and all 16 expected FSV output words.

The two payloads are compact JSON compressed with the repository's zlib fixture codec. JSON preserves compatibility with the legacy GKR reader; no bincode is used. Generation canonicalizes diagnostic source-location labels to repository-relative names. Stored data contains no wall times, process IDs or absolute checkout paths. A separate high-performance CI job regenerates and byte-compares all three files; generation needs about 58 GiB RSS. Reproduce from the repository root:

```sh
RAYON_NUM_THREADS=8 RUST_MIN_STACK=134217728 cargo run -p program_prover --profile cli --features fixture_generation --example hashed_fibonacci_fixture -- target/hashed-fibonacci-refresh
for fixture_file in proof.compact.json.zlib setups.compact.json.zlib manifest.json; do
  cmp "full_statement_verifier/tests/fixtures/hashed_fibonacci/$fixture_file" "target/hashed-fibonacci-refresh/$fixture_file"
done
```

For an intentional program/config change, review the new manifest and replace all three files together. The native Miri-input example checks program identity, production layouts, schedules, full output and NDS exhaustion before writing a derived stream under `target/`. The `miri_fsv` feature opts a host test into the Compression guest's Merkle-opening layout; it keeps host hashing in Rust and changes no normal host or RISC-V selection. The Miri job currently reports the known U02 uninitialized-register-array UB. No diagnostic workarounds are part of this fixture or CI.
