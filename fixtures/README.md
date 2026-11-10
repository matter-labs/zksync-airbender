# Canonical circuit proofs

The canonical set contains one Sec100 proof for each of 14 circuits in each
soundness mode: `PessimisticConjecture` and `EthproofsSoundnessCalc`.
Proofs live in `circuits/<mode>/<circuit>.json.zlib` under this directory.
The mode directories are `pessimistic_conjecture` and `ethproofs_soundcalc`.
G-function has no canonical fixture. Legacy `keccak_special5` remains covered.

Run the sole producer from the repository root:

```sh
RUST_MIN_STACK=16777216 cargo test -p prover --lib --features test --profile cli -- \
  --exact tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs \
  --nocapture --test-threads=1
```

Use the default features, including `deterministic_pow`, and the regular
generated layouts. The producer reads each circuit's generated Sec100 config
for its mode, uses every available core with in-memory WHIR oracles, and
writes one zlib stream of typed compact JSON without a trailing newline.
Proof bytes depend on neither the thread count nor the oracle storage mode.
It regenerates all 28 files and rejects duplicate writes.

`proof_fixtures` pins `flate2` and its `miniz_oxide` compressor because the
currency gates compare complete compressed files. Bumping either version is a
deliberate regeneration step: regenerate the committed fixtures and review the
encoded-byte changes together with the version bump.

The shared recipe is implemented in
[`canonical_fixtures.rs`](../prover/src/tests/gkr/orchestration/canonical_fixtures.rs).
The CPU producer and GPU tests use its explicit circuit-to-workload mapping.
All workloads have a `2^20` cycle bound. Paths below name the binary/text pair
without their `.bin` and `.text` extensions; reads are ordered `u32` values.
`N` is the generated circuit's trace length as `log2(rows)`.

| Circuit(s) | Workload | Reads | Decoder | RAM | N |
| --- | --- | --- | --- | --- | --- |
| `add_sub_lui_auipc_mop`, `shift_binop` | `examples/mop_smoke/app` | `[15, 1]` | full unsigned | 1 GiB | 24 |
| `jump_branch_slt`, `mem_word_only`, `mem_subword_only`, `inits_and_teardowns` | `riscv_transpiler/examples/keccak_f1600/app` | `[15, 1]` | full unsigned | 512 MiB | 24 |
| `unsigned_mul_div` | `examples/hashed_fibonacci/app_blake2_with_compression` | `[15, 1]` | full unsigned | 1 GiB | 23 |
| `bigint_with_extended_control` | `examples/bigint_with_control/app` | `[]` | full unsigned | 1 GiB | 22 |
| `blake2_with_extended_control` | `examples/multi_family_smoke/app_blake2_with_compression` | `[50, 0xDEADBEEF]` | reduced | 1 GiB | 20 |
| `unified_reduced_machine` | `examples/multi_family_smoke/app_blake2_with_compression` | `[50, 0xDEADBEEF]` | reduced | 1 GiB | 23 |
| `keccak_special5` | `riscv_transpiler/examples/keccak_f1600/app` | `[15, 1]` | full unsigned | 512 MiB | 22 |
| `keccak_column_parity`, `keccak_theta_rho`, `keccak_chi5` | `examples/keccak/app` | `[]` | full unsigned | 512 MiB | 22 |

The recipe checks replayed final state, nonempty selected rows and single-instance
capacity. It checks MOP/byte-swap execution and the three new Keccak row counts.
It collects sparse final RAM before expanding the selected inits/teardowns sets.

Compression and unified form one statement. Their challenges come from the
shared memory transcript, final registers/PC/timestamp and sorted RAM top bits,
with deterministic 19-bit memory/delegation PoW. The producer checks that their
memory commitments match the transcript and that the combined permutation
product is ONE. The other circuits use the recipe's fixed external challenges.
No environment filter, suffix or packing override selects canonical inputs.

The gitignored `prover/test_proofs/malicious_*` files serve verifier rejection
tests and have separate forge producers. The canonical producer does not refresh them.

## Currency and GPU agreement

The `Rust CI / tests` job runs the producer command above in the checkout and
fails if `git status` then reports any change under `fixtures/circuits`: a
changed byte, including JSON formatting, or a new file. The producer itself
rejects a committed proof file that it does not write.

The GPU workflow runs `cpu_canonical_matrix_inventory`, which checks the GPU
test registry against the same circuit/mode registry, then runs the 28 listed
`canonical_*` tests. Each case rebuilds the raw recipe, checks the current
circuit's memory caps independently, and compares two queued GPU proofs with
the original committed bytes. Both modes retain the
allocator-baseline, nonce-shape, standalone i/t and unified closure checks.
Native FSV tests assemble the canonical compression/unified pair with freshly
replayed boundary metadata. Whole-program `*_cpu_gpu_proof_diff` diagnostics
remain outside this canonical circuit set.

The [CI job](../.github/workflows/ci.yml) uses runner label
`matterlabs-ci-runner-high-performance` and a 90-minute timeout for proving,
compilation and the remaining checks. The step logs `MemTotal` and
`MemAvailable`; the workflow specifies a runner label rather than a guaranteed
memory capacity.
