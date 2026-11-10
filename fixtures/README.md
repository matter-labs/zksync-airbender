# Canonical circuit proofs

The canonical set contains one Sec100 proof for each of 14 circuits in each
soundness mode: `PessimisticConjecture` and `EthproofsSoundnessCalc`.
Proofs live in `circuits/<mode>/<circuit>.json.zlib` under this directory.
The mode directories are `pessimistic_conjecture` and `ethproofs_soundcalc`.
G-function has no canonical fixture. Legacy `keccak_special5` remains covered.

The producer recipe runs from the repository root:

```sh
fixtures/regenerate.sh                    # both modes, circuits and chains in order
fixtures/regenerate.sh --stage circuits   # only the 28 circuit proofs
fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage base_unified
```

Modes are `pessimistic_conjecture` and `ethproofs_soundcalc`. Stages are
`circuits`, `base_unified`, and `unrolled`. A selected chain stage requires
`--check`; write mode always refreshes a mode's whole chain in order. `--mode`
may select one mode in either operation.

The two canonical producer tests share one body and fix their mode in code:
`tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs_<mode>`.
The script builds and invokes their test executable with `--exact`.

Use the default features, including `deterministic_pow`, and the regular
generated layouts. The producer reads each circuit's generated Sec100 config
for its mode, uses every available core with in-memory WHIR oracles, and
writes one zlib stream of typed compact JSON without a trailing newline.
Proof bytes depend on neither the thread count nor the oracle storage mode.
Each mode emits exactly 14 files and rejects duplicate writes.

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

`fixture_build` builds the CLI, canonical producer test executable, and
`fixture-codec` once. `fixture_currency` runs six independent CPU jobs over
(mode, stage). Each runs the script with `--check`, writes into a temporary root,
and compares complete compressed files with the committed outputs. Every child
reads its committed parent, including when several stages are checked in one
invocation. A stale parent's own stage fails even when a dependent stage passes.
Failed checks retain their temporary outputs and logs and print their location.
The `tests` job checks the exact file inventory, decoding and typed byte
round-trips, then runs native verifier tests.

For downloaded executables, set `FIXTURE_CLI`, `FIXTURE_CANONICAL_PRODUCER`, and
`FIXTURE_CODEC` to their paths. CI requires the executables needed by the selected
stage and invokes no Cargo commands during a currency check. Developers may omit
them to build locally.

`AB_TEST_ARTIFACT_ROOT` selects the repository containing layouts, configs,
workloads, committed parents, and expected outputs. `PROOF_FIXTURES_OUTPUT_ROOT`
is a separate repository-shaped root used only by the canonical producer's
writes. The recipe sets it for `--check` and sets `FSV_DIR` to the selected
repository's tracked guests; neither input location is inferred from the output
root.

The GPU workflow runs `cpu_canonical_matrix_inventory`, which checks the GPU
test registry against the same circuit/mode registry, then runs the 28 listed
`canonical_*` tests. Each case rebuilds the raw recipe, checks the current
circuit's memory caps independently, and compares two queued GPU proofs with
the original committed bytes. Both modes retain the
allocator-baseline, nonce-shape, standalone i/t and unified closure checks.
Native FSV tests assemble the canonical compression/unified pair with freshly
replayed boundary metadata. Whole-program `*_cpu_gpu_proof_diff` diagnostics
remain outside this canonical circuit set.

## Chain artifacts

Each mode has four schema 5 CLI artifacts under `chains/<mode>/`. They use the
tracked `examples/basic_fibonacci/app.bin`, CPU backend, 16 worker threads, and
Compression guests for unrolled, bridge, and final layers. Every artifact has
`program_cycles = 97`; the recipe verifies every proof and rejects absolute
paths inside `Variable at ...` labels.

| Artifact | Input | Additional unrolled layers | Chain entries |
| --- | --- | --- | --- |
| `base` | program | unset | 1 |
| `unified` | `base` | 0 | 3 |
| `unrolled` | `base` | 1 | 2 |
| `unrolled_unified` | `unrolled` | 0 | 4 |

Write mode publishes each parent before its child. Check mode always reads the
committed parents and compares only its own stage's outputs. `base_unified` also
runs the smoke script's wrong-mode and relabel checks on the existing artifacts.
The recipe sets `RECURSION_UNIFIED_SWITCH_CYCLES=52000000`; forced layer counts
bypass that threshold for the chain continuations.

| Fixture | Consumers |
| --- | --- |
| `circuits/<mode>/*` | native, corruption, transpiler, GPU canonical matrix, cost-model drift checks |
| `chains/<mode>/{base,unified}` | CLI verification, currency and soundness smoke checks, typed encoding test |
| `chains/<mode>/{unrolled,unrolled_unified}` | CLI verification, currency and typed encoding test |
