# L1 reference artifacts

The reference is the CLI output for `examples/basic_fibonacci/app.bin`:

- `recursion_unified.json`: converged Standard unified seed.
- `l1_feeder.json`: terminal C proof after `(First, A, 2)`, `(Recurrent, A, 1)`, `(Recurrent, C, 1)`.
- `l1.json`: the full CLI L1 artifact, including the C proof, setups, chain and `.l1` wrap bundle.

These files use compact typed JSON with no trailing newline. Backend selection
is not stored; timings are transient and remain available to the batch summary.
Regenerate after changes to guests, circuits, configs, proof formats or L1 proving.
Do not convert existing JSON to refresh the reference: run the CLI.

From the repository root, the CPU producer commands are:

```bash
export CARGO_BUILD_JOBS=12 RUST_MIN_STACK=1073741824
cargo build --release -p cli
cli=target/release/cli
bin=examples/basic_fibonacci/app.bin
dir=prover_pipeline/fixtures/l1_reference_2p21
export RECURSION_UNROLLED_BLAKE=blake2_with_compression
export RECURSION_BRIDGE_BLAKE=blake2_with_compression
export RECURSION_FINAL_BLAKE=blake2_with_compression
export RECURSION_UNIFIED_SWITCH_CYCLES=52000000
mode=(--soundness-mode pessimistic-conjecture)
"$cli" prove --bin "$bin" --target recursion-unified --backend cpu "${mode[@]}" \
  --output-dir "$dir" --output-file recursion_unified.json
"$cli" continue-proof --proof "$dir/recursion_unified.json" --bin "$bin" \
  --target l1-feeder --backend cpu "${mode[@]}" --output-dir "$dir" --output-file l1_feeder.json
"$cli" continue-proof --proof "$dir/l1_feeder.json" --bin "$bin" \
  --target l1 --backend cpu "${mode[@]}" --output-dir "$dir" --output-file l1.json
git status --porcelain -- "$dir"
```

A current reference produces an empty status. The Blake modes and switch
threshold pin seed construction; continuations use the artifact's Blake tags.
L1 targets require Compression modes. `deterministic_pow` is a default CLI feature.

For GPU production, build with `--features gpu`, replace `--backend cpu` with
`--backend gpu --gpu-memory-preset 21gib`, and run each proving command under
`.agents/bin/with_gpu_lock.sh`. Builds and CPU verification do not take that lock.
The combined gate proves the feeder chain and wrap in one session:

```bash
.agents/bin/with_gpu_lock.sh "$cli" continue-proof --proof "$dir/recursion_unified.json" \
  --bin "$bin" --target l1 --backend gpu --gpu-memory-preset 21gib "${mode[@]}" \
  --output-dir output/l1 --output-file l1.json
"$cli" verify --proof output/l1/l1.json --bin "$bin" "${mode[@]}"
cmp "$dir/l1.json" output/l1/l1.json
```

CPU CI natively verifies the committed seed and C artifact. CLI verification of
`l1.json` checks its envelope and native C sidecar; EVM verification checks the
Proth120 wrap proof. The full reference's byte identity is checked with raw `cmp`.
The combined 21 GiB run and backend byte comparisons require fresh execution;
this README makes no current resource or timing claim.

To refresh the setup frontier after producing `l1.json`, then check EVM outputs:

```bash
cargo test -p prover_pipeline --release --lib l1_reference::export_l1_wrap_setup_frontier -- --exact --ignored
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
git status --porcelain -- verifier_evm/generated_contracts verifier_evm/debug_data
verifier_evm/generated_contracts/run_merged.sh
```

The [EVM harness README](../../../verifier_evm/generated_contracts/l1_wrap_2p21/README.md)
describes deployment and calldata.
