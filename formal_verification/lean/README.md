# Circuit verification

<!-- lean-context: Clean.Circuit.Expression Clean.Circuit.Operations Clean.Circuit.Lookup Clean.Specs.Keccak256 -->
<!-- source-names: CI FV_ROOT -->

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists every circuit, checked coverage
and outstanding validation, with historical evidence identified separately.

[Compiler review](Airbender/Review/Compiler/README.md) states captured base-field
arithmetic preservation and the conditional executor bridge.
[GKR compiler evidence](GKR_COMPILER_VERIFICATION.md) separates its supporting
wiring/lookup/RAM results from historical checkpoints.

The [findings audit](FINDINGS.md) records accepted counterexamples and unresolved
bindings, with links to their assumptions and evidence.

The proof path is:

```text
no-cache JSON → native Clean constraints → Sail execution (or pinned custom spec)
```

Claims are conditional on explicit interfaces. The imported richer constraints are
the current target. Captured compiled/cached base-field arithmetic preservation
is proved for 22 instances. New compiler execution APIs derive lookup membership
and helper ranges from physical-row arithmetic and exact matching of actual native encoding/leaf tuples,
without canonical framing. Native field/mask/helper identities transport those
tuples to source operands; final sampled balance-to-exact matching and physical
multiplicity binding remain explicit abstractions. Exact state/RAM matching and
public boundaries remain explicit. Supplied-program
wrappers require compatibility with retained decoder tables. All 14 native row
compositions and public wrappers compile; execution/public modules also pass
selected-module replay at a 32 MiB Lean thread stack. The selected 3279-module/
10-test frontend passes normal Lake no-build freshness and artifact-hash checking
without repairs. Its manifests bind only the selected scope; full project/runtime,
environment, independent replay, negative-control and Linux/cold-run validation
remain pending. See [current evidence](VERIFICATION_STATUS.md#current-focused-validation). Cryptographic argument
soundness and universal Rust compiler correctness remain outside the model.

## Read these first

The [Review guide](Airbender/Review/README.md) has two routes:
[individual circuit review](Airbender/Review/Circuits/README.md) and
[whole-trace review](Airbender/Review/Trace/README.md).
Directory READMEs explain the relevant references, mappings, assumptions and scope.

[Properties](Airbender/Review/Helpers/Properties.lean) defines soundness,
completeness and the observable circuit relation. Shared helpers are grouped by
[topic](Airbender/Review/Helpers/README.md); properties do not require decoder or
memory-history review. Supporting calculations remain in Proofs; Import has a
separate fidelity boundary.

## Clean and Sail

Clean is pinned at `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
[Preparation](scripts/prepare_clean.py) checks original source hashes before applying
Lean `v4.31.0` compatibility fixes: a tactic import, factory registration metadata,
and explicit proof reductions. Constraint semantics, algorithms and theorem
statements are unchanged; repaired proof terms are kernel-checked and axiom-audited.
The original Keccak permutation reference compiles unchanged; the [Theta column](Airbender/Review/Circuits/Keccak/Theta.lean) and [two-call Chi row](Airbender/Review/Circuits/Keccak/Chi.lean) claims use its `thetaXor` and `chi` directly. We use Clean's native
`Expression`, `FlatOperation.assert`, `StaticTable`, `FlatOperation.lookup`,
`Environment` and `ConstraintsHoldFlat`.
The witness-generation DSL and full `FormalCircuit` bundle are not used.
Airbender's two-16-bit-limb representation is preserved.

The reference uses [unmodified upstream Sail clauses](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [their generated Lean definitions](generated/sail-rv32/SailRV32.lean).
The original ADD/SUB clause is `execute(RTYPE(...))`; ADDI is `execute(ITYPE(...))`;
LUI/AUIPC use `execute(UTYPE(...))`. The Lean interface calls the generated
`execute_RTYPE`, `execute_ITYPE` and `execute_UTYPE` directly.
Unsigned division uses the original `execute_DIV`/`execute_REM` clauses from
[the M-extension source](vendor/sail-riscv/source/model/extensions/M/mext_insts.sail).
[Provenance and regeneration](generated/sail-rv32/README.md) record model/compiler/runtime
pins. The normal four-byte nextPC assignment is extracted verbatim from upstream
`run_hart_active` and compiled by Sail, then composed with execution and `tick_pc`.
Extraction and path selection remain unchecked connections; full fetch/exception
handling and memory arguments are outside the claim. Standard instructions have no local replacement spec;
custom arithmetic uses the [pinned project definitions](vendor/airbender/00-master.md#supported-instruction-set-and-custom-operations).
Representation and execution lemmas live in `Proofs/Arithmetic/Word.lean` and
`Proofs/Sail/RiscV.lean`.

The Blake2 round query proofs reuse [generic row expressions](Airbender/Proofs/Blake2G/FrameQueryEntries.lean)
and [row arithmetic](Airbender/Proofs/Blake2G/FrameQueryRows.lean). Separate
[bindings](Airbender/Proofs/Blake2G/FrameQueryBindings.lean) check the actual imported G
lookups; each native column and diagonal call checks its own imported expressions,
then supplies its frame to the shared arithmetic. Existing public theorem statements
and actual table membership obligations remain unchanged. Definition-only modules and
family-local native effects avoid the combined delegation-operation implementation.
The [focused boundary check](scripts/check_proof_boundaries.py) verifies these source
import paths without compiling.

## Reproduce

Use Python 3.11+, the pinned Lean `leanprover/lean4:v4.31.0` and Rust
`nightly-2026-08-09` from the repository toolchain files. Run the following in
Bash from `formal_verification/lean`, with the global FV worker idle:

```sh
set -euo pipefail
FV_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/airbender-fv.XXXXXX")"
export CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 MATHLIB_NO_CACHE_ON_UPDATE=1
# Debug symbols are unnecessary for deterministic setup exports.
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
export CARGO_TARGET_DIR="$FV_ROOT/cargo"

# A lightweight orchestrator: its process controls guard their own children.
# Run these on Linux itself before Linux compiler work; Darwin cannot verify
# Linux pidfd/subreaper behavior. Do not wrap this orchestrator in another guard.
python3 -m unittest discover -s scripts -p test_bounded_fv.py -v
python3 scripts/compilation_pool/test_pool.py --process-tests --process-output "$FV_ROOT/pool-controls"
fv() {
  label="$1"
  shift
  python3 scripts/bounded_fv.py --mib 2560 --resident-mib 5120 --seconds 900 \
    --log "$FV_ROOT/$label.log" -- "$@" | tee "$FV_ROOT/$label.guard.jsonl"
}

# Bootstrap only the pinned Mathlib cache CLI, serially, before Clean patches.
# Ordinary Lake loads the exact manifest; do not run lake update.
modules=(Batteries.Data.Array.Match Batteries.Data.String.Basic
  Batteries.Data.String.Matcher Batteries.Tactic.OpenPrivate Cache.Lean
  Cache.IO Cache.Hashing Cache.Init Cache.Requests Cache.Main)
for module in "${modules[@]}"; do
  fv "cache-olean-$module" lake --no-cache build "+$module:olean"
done
for module in "${modules[@]}"; do
  fv "cache-native-$module" lake --no-cache build "+$module:o"
done
fv cache-executable lake --no-cache build cache
fv mathlib-cache lake exe cache get
fv prepare-clean python3 scripts/prepare_clean.py

# Copy the retained Cargo lock only when absent; an existing lock must match.
fv native-lock python3 scripts/check_setup_artifacts.py --prepare-lock
fv provenance-controls python3 -m unittest discover -s scripts -p test_setup_provenance.py -v
families=(add-sub jump-branch mul-div shift-binop word-memory subword-memory
  unified bigint blake-g blake-round keccak inits-and-teardowns)
for family in "${families[@]}"; do
  fv "regenerate-$family" env -u CI -u RUST_MIN_STACK python3 scripts/check_setup_freshness.py \
    regenerate "$family" --work-dir "$FV_ROOT/native"
done
for family in "${families[@]}" decoder-smoke; do
  fv "export-$family" env -u CI -u RUST_MIN_STACK python3 scripts/check_setup_freshness.py \
    export "$family" --work-dir "$FV_ROOT/native"
done
dep_args=()
while IFS= read -r -d '' file; do dep_args+=(--dep-info "$file"); done \
  < <(find "$CARGO_TARGET_DIR/debug" -type f -name '*.d' -print0)
fv native-receipts python3 scripts/check_setup_freshness.py verify \
  --work-dir "$FV_ROOT/native" "${dep_args[@]}"

# Re-export actual cached and uncached compiler output after Rust/source changes.
fv compiler-export env -u CI -u RUST_MIN_STACK python3 scripts/export_gkr_translations.py --output "$FV_ROOT/compiler"
fv compiler-retained python3 scripts/check_gkr_translations.py
fv compiler-fresh python3 scripts/check_gkr_translations.py --directory "$FV_ROOT/compiler"
diff -qr artifacts/compiler "$FV_ROOT/compiler"
fv compiler-provenance-controls python3 -m unittest discover -s scripts -p test_gkr_translation_provenance.py -v
fv compiler-native-requests python3 scripts/generate_native_lookup_requests.py --check

# Frontends own their aggregate guard; use no outer guard.
# Source freshness defaults to four bounded read-only query workers.
python3 scripts/check_lean.py --guard scripts/bounded_fv.py --output "$FV_ROOT/lean"
sysroot="$(lean --print-prefix)"
python3 scripts/check_axioms.py --guard scripts/bounded_fv.py \
  --sysroot "$sysroot" --output "$FV_ROOT/axioms" \
  --dispositions scripts/axiom_dispositions.json
python3 scripts/check_kernel_replay.py --guard scripts/bounded_fv.py \
  --sysroot "$sysroot" --output "$FV_ROOT/replay" \
  --stack-mib 32 --fresh-project --ledger .lake/verification/replay-ledger \
  --axiom-result "$FV_ROOT/axioms/axiom-result.json"
python3 scripts/check_assurance_controls.py --guard scripts/bounded_fv.py \
  --sysroot "$sysroot" --output "$FV_ROOT/assurance-controls" \
  --ledger .lake/verification/replay-ledger
```

The 25 native jobs execute twelve production generators and thirteen exports,
including the derived decoder smoke fixture. Their final verification checks
execution receipts, complete JSON identity and the scoped native build's dep-info.
`CI` must be absent for generators and smoke tests; `CI=false` still skips them.

The Lean frontend discovers every concrete Airbender, Tests and retained
Sail module. Its [bounded compilation pool](scripts/compilation_pool/README.md)
checks cached ordinary Lake freshness with four workers by default,
under one combined resource owner. Dirty rebuilds and high-memory work run
exclusively. It serializes the actual executable
native closures, and checks the library, both executables, importer runtime,
direct axiom smoke reports, guide references, proof boundaries and source/evidence
pins. A direct Lean axiom report can omit dependencies in imported constructor
types; the compiled-environment walk, baseline and reviewed dispositions are the
standard-axiom dependency gate. Its verified source/object/job snapshot lets the review check inspect the
same compiled tree without starting an aggregate build. The environment-origin
proof audit, full independent kernel replay and isolated direct/transitive false
proof controls are separate gates. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed; all preserved audit roots remain required. Importer
regressions do not prove parsing fidelity.

All real workers share `/tmp/airbender-fv-single-worker.lock` and one aggregate
resource budget: 2560 MiB footprint, 5120 MiB bounded resident and 900 seconds;
the review stage alone permits 1800 seconds. Darwin uses its libproc footprint/RSS.
Linux footprint is the approximate sum of anonymous memory, proportional shared
memory, swap and huge pages; bounded resident omits swap. Reclaimable mapped files
are excluded from these Linux caps; total RSS remains telemetry. Sampled budgets
are not exact cgroup enforcement. Commands and peak metrics are retained in receipts.

Independent replay passes Lean an explicit 32 MiB thread stack on every host,
using --tstack=32768, and records it in the ledger identity. Linux also sets the
process stack limit to 32 MiB. On Darwin, the OS rejects process stack-limit
changes; replay leaves that limit inherited and records it while still selecting
the Lean thread stack. The Linux process-stack runtime control is skipped on
Darwin. This default remains provisional: the five reported deep-recursion
failures are not established as fixed until full current-head replay passes.

The --fresh-project option replays project roots on every run. The persistent
ledger under .lake/verification/replay-ledger reuses dependency entries only for
identical compiled bytes and tool identity; saved report paths are relative.
The ledger must come from a trusted checking context: matching hashes cannot
authenticate a fabricated pass report. CI restores and saves this ledger only
on the repository's default branch. Other refs use a fresh per-attempt ledger
outside the checkout and replay dependencies as well as project roots.
A failed bounded job stops the run; exact commands, peaks and failed stages remain
under FV_ROOT.

For scale, the historical `1d3e4bdbb` clean parallel build took 1 h 39 min on eight
cores. Its serial cold reproduction was estimated at roughly 7.5 h plus about
15 h of replay; thousands of subsequent compiler modules make these figures
historical guidance, not a current runtime estimate. Current peak memory, stack
and cold-cache duration require measurement on the actual Linux host.

The [formal-verification workflow](../../.github/workflows/formal-verification.yml)
is temporarily advisory and selected for formal-verification, circuit-source and
pinned-evidence changes. Branches have independent queues. Source/dependency caches
support warm starts; trusted default-branch runs also reuse their replay ledger.
Immutable snapshots
are saved after bootstrap, native setup/compiler export, Lean checking and replay,
including bounded stage failures. Restore first selects the same source and then
compatible toolchain/dependency snapshots; normal freshness and integrity checks
still run. The replay ledger remains separate from normal build caches.

CI stops long work at a shared 22-hour deadline within the 24-hour job, reserving
time for cleanup, partial-cache saves and log upload. Each real worker retains its
existing resource/time guard. A bounded stage timeout fails that run; it never
converts partial work into a pass. Default-branch dependency replay entries may
resume, while project roots replay freshly on every complete attempt. PR runs
do not reuse pass JSON from earlier PR attempts. Cold runtime and
whether the current library/replay fit these stage windows remain unmeasured;
partial reuse improves recovery without establishing feasibility or validation.

A cached build is not a final pass marker. Selectively required status follows a
complete Linux pass. Remote CI, full current-head auditing/replay and empty-cache
reproduction remain pending; these commands do not claim they passed. The reviewed
disposition file records intended baseline exceptions, not a successful full
baseline regeneration.

After the toolchain/cache/preparation steps above, a focused trace check is:

```sh
python3 scripts/check_lean.py --guard scripts/bounded_fv.py \
  --output "$FV_ROOT/trace-import" \
  --module Tests.TraceImport --module Airbender.Checks.TraceAxioms
fv trace-axioms lake env lean Airbender/Checks/TraceAxioms.lean
```

This scope compiles the importer checks and audits the six ordinary families:
ADD/SUB, word-memory, jump/branch/SLT, MUL/DIV, shift/binop and subword memory,
including REV8, rollover/rejection histories and public initialization. The full
frontend's importer runtime additionally executes the timestamp/address/value,
physical-placement, decoder-selector and storage-polarity mutation guards. The primary public surface is
[Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean), with the native
matching and initial-clock conditions in [Context/Model.lean](Airbender/Review/Helpers/Context/Model.lean).
The history fixtures check rejection of an unmatched previous-write timestamp
and complete per-address paths with interleaved accesses and changing values.
A changed operand/result pair satisfies the local ADD constraints but is rejected
by native matching because the fabricated read has no matching previous write.
The nonzero-register fixture checks the explicit initialization writes required
by Clean's zero-initial online-memory semantics.
The [initial-image constructor](Airbender/Review/Helpers/Memory/InitialImage.lean) reads
public Sail state directly. Its fixtures check nonzero GPRs, x0, little-endian
RAM and rejection of missing cells; extraction proves initial bounds and uniqueness.

With the Lean 4 VS Code extension, open this project folder and inspect a scratch
file in the Infoview:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
