# Canonical circuit proofs

The canonical set contains one Sec100 proof for each of 14 circuits in each
soundness mode: `PessimisticConjecture` and `EthproofsSoundnessCalc`.
`PessimisticConjecture` uses `<circuit>_sec_100_gkr_proof.json`;
`EthproofsSoundnessCalc` adds `_ethproofs_soundcalc` after `sec_100`.
G-function has no canonical fixture. Legacy `keccak_special5` remains covered.

Run the sole producer from the repository root:

```sh
RUST_MIN_STACK=16777216 cargo test -p prover --lib --features test --profile cli -- \
  --exact tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs \
  --nocapture --test-threads=1
```

Use the default features, including `deterministic_pow`, and the regular
generated layouts. The producer reads each circuit's generated Sec100 config
for its mode, uses eight worker threads, and writes pretty JSON without a
trailing newline. It regenerates all 28 files and rejects duplicate writes.

The shared recipe is implemented in
[`canonical_fixtures.rs`](../src/tests/gkr/orchestration/canonical_fixtures.rs).
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

The `malicious_*` files serve verifier rejection tests and have separate forge
producers. The canonical producer does not refresh those files.

## Currency and GPU agreement

The `Rust CI / tests` job runs the producer command above in the checkout and
fails if `git status` then reports any change under `prover/test_proofs`: a
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

Two full CPU passes measured 2,144.78 and 2,178.91 seconds, with peak RSS of
66,624,667,648 and 66,554,937,344 bytes respectively. They used eight workers and
the optimized CLI profile and produced identical bytes for every entry. The
[CI job](../../.github/workflows/ci.yml) uses runner label
`matterlabs-ci-runner-high-performance` and a 90-minute timeout for proving,
compilation and the remaining checks.

Existing [Rust CI run 42184209057](https://github.com/matter-labs/zksync-airbender/actions/runs/42184209057)
provides supporting capacity evidence at `3af2e8def`:

- [`cli_smoke_verify`](https://github.com/matter-labs/zksync-airbender/actions/runs/42184209057/job/127780580344)
  passed on the same runner label in 38m53s. Its CPU command uses
  `soundness_mode_smoke.sh ... cpu --cycles-bound 16777216 --worker-threads 8`.
  The matching command measured **116,486,524 KiB** peak RSS (about 119.3 GB)
  locally, with zero swaps. Completion in CI supports headroom above the
  canonical producer's 66.6 GB peak. This inference assumes comparable effective
  memory across same-label pods, comparable workload RSS and no swap in CI;
  the CI memory limit and swap use were not measured.
- The [`tests` job](https://github.com/matter-labs/zksync-airbender/actions/runs/42184209057/job/127780579911)
  passed in 40m05s, including the old basic producer. Adding the entire measured
  36-minute replacement pass, without credit for removing the old producer,
  gives about 76 minutes within the 90-minute budget. This is an allowance
  estimate; the new complete job has not been timed.

The step logs `MemTotal` and `MemAvailable`; the workflow specifies a runner
label rather than a guaranteed memory capacity.
