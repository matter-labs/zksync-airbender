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
`circuits`, `base_unified`, `unrolled`, `l1_feeder`, and `l1`. Selecting
`base_unified` or `unrolled` requires `--check`; without a stage, write mode
refreshes a mode's circuits and whole chain in order. The L1 stages can also be
written individually and select `pessimistic_conjecture` by default; explicitly
requesting them in `ethproofs_soundcalc` is rejected. `--mode` may select one
mode in either operation.

The two canonical producer tests share one body and fix their mode in code:
`tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs_<mode>`.
Locally the script runs them through `cargo test` with `--exact`; with
`FIXTURE_CANONICAL_PRODUCER` set it invokes that prebuilt test executable instead.

Use the default features, including `deterministic_pow`, and the regular
generated layouts. The producer reads each circuit's generated Sec100 config
for its mode, uses every available core with in-memory WHIR oracles, and
writes one zlib stream of typed compact JSON without a trailing newline.
Proof bytes depend on neither the thread count nor the oracle storage mode.
Each mode emits exactly 14 files.

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

Every circuit uses the recipe's fixed external challenges. The compression
and unified circuit proofs keep the shared `CompressionSmoke` workload and are
independent circuit fixtures. Whole-statement FSV tests use the chain artifacts.
No environment filter, suffix or packing override selects canonical inputs.

The gitignored `prover/test_proofs/malicious_*` files serve verifier rejection
tests and have separate forge producers. The canonical producer does not refresh them.

## Currency and GPU agreement

`fixtures/regenerate.sh --check` writes into a temporary root and compares
complete compressed files with the committed outputs. Every child reads its
committed parent, including when several stages are checked in one invocation.
A stale parent's own stage fails even when a dependent stage passes. Failed
checks retain their temporary outputs and logs and print their location.
With `FIXTURE_BACKEND=gpu` the chain stages are proved on GPU and compared with
the same committed CPU artifacts; the GPU `canonical_*` tests compare GPU
circuit proofs with the committed bytes. Whole-program `*_cpu_gpu_proof_diff`
diagnostics remain outside this canonical circuit set. CI runs six Standard
CPU jobs and one pessimistic-only CPU `l1_feeder` job in `fixture_currency`;
GPU checks run in the GPU workflow's `chains` shard.

For prebuilt executables, set `FIXTURE_CLI`, `FIXTURE_CANONICAL_PRODUCER`, and
`FIXTURE_CODEC` to their paths; the script builds any that are unset with Cargo.
With `FIXTURE_TRUSTED_PARAMS` set to a directory, the recipe's Standard-stage
`verify` passes the trusted params kept there and computes a missing file once.
Without it, as in the CPU currency jobs, that `verify` derives them from the
program. The smoke checks compute their own trusted params and always pass them.
The `l1_feeder` and `l1` stages always derive their parameters from the program:
the shared cache contains only Standard records, and supplied Standard records
must refuse L1 verification.

`AB_TEST_ARTIFACT_ROOT` selects the repository containing layouts, configs,
workloads, committed parents, and expected outputs. `PROOF_FIXTURES_OUTPUT_ROOT`
is a separate repository-shaped root used only by the canonical producer's
writes. The recipe sets it for `--check` and sets `FSV_DIR` to the selected
repository's tracked guests; neither input location is inferred from the output
root.

## Chain artifacts

Each mode has four standard schema 5 CLI artifacts under `chains/<mode>/`.
`pessimistic_conjecture` additionally has `l1_feeder` and `l1`; ethproofs refuses
both L1 targets. They use the tracked `examples/basic_fibonacci/app.bin`, CPU
backend on every available core, and Compression guests for unrolled, bridge,
and final layers. Every artifact has `program_cycles = 97`; the recipe natively
verifies its proof and rejects absolute paths inside `Variable at ...` labels.
The optional `l1` bundle is serialized only when present, so the eight standard
chain artifacts keep their schema-5 encoding.

| Artifact | Input | Additional unrolled layers | Chain entries |
| --- | --- | --- | --- |
| `base` | program | not read | 1 |
| `unified` | `base` | 0 | 3 |
| `unrolled` | `base` | 1 | 2 |
| `unrolled_unified` | `unrolled` | 0 | 4 |
| `l1_feeder` (pessimistic only) | `unified` | fixed feeder schedule | 6 |
| `l1` (pessimistic only) | `l1_feeder` | wrap; same C sidecar | 6 |

The `prover_pipeline` test `committed_chain_encoding` checks each committed
artifact's target, chain entries and `program_cycles`.

Write mode publishes each parent before its child. Check mode always reads the
committed parents and compares only its own stage's outputs. On the CPU backend
`base_unified` also runs the smoke script's wrong-mode and relabel checks on the
existing artifacts.

| Fixture | Consumers |
| --- | --- |
| `circuits/<mode>/*` | native, corruption, transpiler, GPU canonical matrix, census price inputs |
| `chains/<mode>/base` | CLI verification, currency, soundness smoke checks, typed encoding; census base guest fit and gates |
| `chains/<mode>/unified` | CLI verification, currency, soundness smoke checks, typed encoding; unified FSV acceptance and rejection |
| `chains/<mode>/unrolled` | CLI verification, currency, typed encoding; census recursion guest fit and gates |
| `chains/<mode>/unrolled_unified` | CLI verification, currency, typed encoding; unified FSV acceptance and rejection |
| `chains/pessimistic_conjecture/l1_feeder` | native CLI verification, feeder tampering and trusted-chain tests; GPU L1 currency and continuation tests |
| `chains/pessimistic_conjecture/l1` | CLI envelope and native C-sidecar verification; wrap/frontier tests; EVM contract and calldata producers; GPU wrap parity |

## L1 production and EVM checks

The shared `unified` artifact is the converged Standard seed. `l1_feeder` is the
terminal C proof after `(First, A, 2)`, `(Recurrent, A, 1)`, `(Recurrent, C, 1)`.
`l1` contains that C proof, setups, chain and the `.l1` Proth120 wrap bundle.
All are typed compact JSON, compressed as one zlib stream with no trailing
newline. Backend selection is not stored; timings remain transient for the
batch summary. Regenerate after changes to guests, circuits, configs, proof
formats or L1 proving. Do not convert existing JSON to refresh these files:
run the CLI through the recipe.

The recipe pins the three recursion Blake modes to `blake2_with_compression`
and `RECURSION_UNIFIED_SWITCH_CYCLES=52000000` for seed construction;
continuations use the artifact's Blake tags. L1 targets require Compression
modes. Use default CLI features, including `deterministic_pow`. From the
repository root, produce the two L1 files on the CPU:

```bash
export CARGO_BUILD_JOBS=12 RUST_MIN_STACK=1073741824
fixtures/regenerate.sh --mode pessimistic_conjecture --stage l1_feeder
fixtures/regenerate.sh --mode pessimistic_conjecture --stage l1
git status --porcelain -- fixtures/chains/pessimistic_conjecture
```

The first command reads the committed `unified.json.zlib`; the second reads
`l1_feeder.json.zlib`. CPU wrap production must stay available for local
regeneration, but it never runs in CI. CPU CI checks `l1_feeder` currency and
natively verifies the committed seed and terminal C artifact. CLI verification of `l1.json.zlib` checks its envelope and native
C sidecar; EVM verification checks the Proth120 wrap proof.

GPU CI checks both L1 stages against complete compressed CPU artifacts. It
reuses prebuilt executables just like the standard GPU chain parity step.
Standard stages share trusted parameters; L1 verification derives its parameters
from the program because the Standard cache has no L1 records. For local checks, build the CLI with `--features gpu`, set
`FIXTURE_CLI` to that binary and `FIXTURE_CODEC` to the built codec, and run each
proving command under the GPU lock:

```bash
export FIXTURE_BACKEND=gpu
.agents/bin/with_gpu_lock.sh fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage l1_feeder
.agents/bin/with_gpu_lock.sh fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage l1
```

CPU verification and builds do not take the GPU lock. `--check` compares the
entire compressed file with `cmp`; a successful check means unchanged bytes.
The recipe makes no current resource or timing claim.

After producing `l1.json.zlib`, refresh the setup frontier and check EVM outputs:

```bash
cargo test -p prover_pipeline --release --lib l1_reference::export_l1_wrap_setup_frontier -- --exact --ignored
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
git status --porcelain -- verifier_evm/generated_contracts verifier_evm/debug_data
verifier_evm/generated_contracts/run_merged.sh
```

The [EVM harness README](../verifier_evm/generated_contracts/l1_wrap_2p21/README.md)
describes deployment and calldata.

## Census tables

`build.sh` rebuilds the registered guests and emits all four census tables from
committed CPU fixtures. Emission proves nothing and requires no GPU or local
corpus. To emit again after refreshing chains:

```sh
RUST_MIN_STACK=16777216 cargo test -p full_statement_verifier --profile cli \
  --features host_utils,verifiers --test cost_model_trace emit_census_tables -- --exact --ignored
```

After a guest change, run `build.sh`, `fixtures/regenerate.sh`, then emission
again. The first emission requires the rebuilt guest to accept the old chain.
If it rejects it, regenerate the chains before emitting; failed traces never
supply a table. The table's guest digest remains pinned.

The prefix tracing, intercept fit and acceptance limits are described in
[`cost_model_trace.rs`](../full_statement_verifier/tests/cost_model_trace.rs).
