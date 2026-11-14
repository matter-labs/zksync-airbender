# Canonical circuit proofs

The Standard canonical set contains one Sec100 proof for each of 14 circuits in each
soundness mode: `PessimisticConjecture` and `EthproofsSoundnessCalc`.
Proofs live in `circuits/<mode>/<circuit>.json.zlib` under this directory.
The mode directories are `pessimistic_conjecture` and `ethproofs_soundcalc`.
G-function has no canonical fixture. Legacy `keccak_special5` remains covered.
Pessimistic-conjecture mode also has the canonical special-profile fixtures
`compression.json.zlib` and `compression_final.json.zlib`. The `circuits` stage
produces them from the shared fixed workload.

The producer recipe runs from the repository root:

```sh
fixtures/regenerate.sh                    # both modes, circuits and chains in order
fixtures/regenerate.sh --stage circuits   # only canonical circuit proofs
fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage base_unified
```

Modes are `pessimistic_conjecture` and `ethproofs_soundcalc`. Stages are
`circuits`, `base_unified`, `unrolled`, `compression`, and `l1`. Selecting
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
The mode-specific inventory is defined in `proof_fixtures`.

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
| `unified_reduced_machine`, `compression`, `compression_final` | `examples/multi_family_smoke/app_blake2_with_compression` | `[50, 0xDEADBEEF]` | reduced | 1 GiB | 23 (22 for `compression_final`) |
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

## Currency checks

`fixtures/regenerate.sh --check` writes into a temporary root and compares
complete compressed files with the committed outputs. Every child reads its
committed parent, including when several stages are checked in one invocation.
A stale parent's own stage fails even when a dependent stage passes. Failed
checks retain their temporary outputs and logs and print their location.
CPU CI checks canonical circuits, Standard chains and the pessimistic-only
compression chain in `fixture_currency`.

For prebuilt executables, set `FIXTURE_CLI`, `FIXTURE_CANONICAL_PRODUCER` and
`FIXTURE_CODEC`; the script builds any that are unset with Cargo.
With `FIXTURE_TRUSTED_PARAMS` set to a directory, verification reuses the records
kept there and computes a missing file once. Pessimistic records include
compression; other modes stop at `recursion-unified`. Without the cache,
verification derives parameters from the program. The soundness smoke checks
compute and pass their own records.

`AB_TEST_ARTIFACT_ROOT` selects the repository containing layouts, configs,
workloads, committed parents, and expected outputs. `PROOF_FIXTURES_OUTPUT_ROOT`
is a separate repository-shaped root used only by the canonical producer's
writes. The recipe sets it for `--check` and sets `FSV_DIR` to the selected
repository's tracked guests; neither input location is inferred from the output
root.

## Chain artifacts

Each mode has four standard schema 5 CLI artifacts under `chains/<mode>/`.
`pessimistic_conjecture` additionally has `compression` and `l1`; ethproofs refuses
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
| `compression` (pessimistic only) | `unified` | fixed compression schedule | 6 |
| `l1` (pessimistic only) | `compression` | wrap; same CompressionFinal sidecar | 6 |

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
| `chains/pessimistic_conjecture/compression` | native CLI verification, compression tampering and trusted-chain tests; GPU L1 currency and continuation tests |
| `chains/pessimistic_conjecture/l1` | CLI envelope and native CompressionFinal-sidecar verification; wrap/frontier tests; EVM contract and calldata producers; GPU wrap parity |

## L1 production and EVM checks

The pessimistic chain fixtures are `chains/pessimistic_conjecture/compression.json.zlib`
and `l1.json.zlib`. The compression recipe reads the committed `unified.json.zlib`;
the L1 recipe reads the committed compression chain. The L1 artifact retains the
CompressionFinal sidecar and adds its Proth120 proof and operation-mode bundle.

Regenerate through the CLI after guest, circuit, config or format changes.
Use default CLI features, including `deterministic_pow`, from the repository root:

```bash
export CARGO_BUILD_JOBS=12 RUST_MIN_STACK=1073741824
fixtures/regenerate.sh --mode pessimistic_conjecture --stage compression
fixtures/regenerate.sh --mode pessimistic_conjecture --stage l1
git status --porcelain -- fixtures/chains/pessimistic_conjecture
```

CPU CI checks compression currency. CPU wrap production is available for local
regeneration. CLI verification of the L1 artifact checks its envelope, chain and
native CompressionFinal sidecar; the EVM verifier checks the Proth120 proof.
The Standard stages use fixed Compression Blake modes. The unrolled-to-unified
switch threshold is the library default unless `RECURSION_UNIFIED_SWITCH_CYCLES`
is set; the recipe does not override it.

The compression circuit fixtures are independent canonical proofs, produced and
checked by the `circuits` stage. The Software-mode Miri case reads `compression`
through the circuit input producer and asserts executed multiproof coverage.

The schedule and input checks live in `prover_pipeline/src/lib.rs`;
[l1_tests.rs](../prover_pipeline/src/l1_tests.rs) owns frontier export and
native compression refusal tests. After producing the L1 fixture, refresh its
setup frontier and EVM outputs:

```bash
cargo test -p prover_pipeline --release --lib l1_tests::export_l1_wrap_setup_frontier -- --exact --ignored
cargo test -p verifier_evm --release --test generate_contracts -- --ignored
cargo test -p verifier_evm --release --test flatten_calldata -- --ignored
git status --porcelain -- verifier_evm/generated_contracts verifier_evm/debug_data
verifier_evm/generated_contracts/run_merged.sh
```

The [EVM harness README](../verifier_evm/generated_contracts/l1_wrap/README.md)
describes deployment and calldata.

## GPU checks

The GPU canonical matrix checks every registered circuit fixture against the
same committed bytes, including `compression` and `compression_final` in
pessimistic mode. The inventory test binds the matrix to the mode-specific
canonical registry.

The GPU workflow's `chains` shard checks Standard chains in both modes and
the pessimistic `compression` and `l1` chains through the shared recipe.
Before proving, it compares CPU and GPU trusted records byte for byte; GPU
record construction logs the context's actual peak allocation per record.
The shared cache includes compression records and no L1 wrap record.

For local currency checks, build the GPU CLI and codec before taking the
device lock, set `FIXTURE_CLI` and `FIXTURE_CODEC` to those executables,
then run one recipe per hold:

```bash
export FIXTURE_BACKEND=gpu
.agents/bin/with_gpu_lock.sh fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage compression
.agents/bin/with_gpu_lock.sh fixtures/regenerate.sh --check --mode pessimistic_conjecture --stage l1
```

Builds and CPU verification do not take the GPU lock. The currency recipe
compares the complete compressed files; it makes no resource or timing claim.

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
