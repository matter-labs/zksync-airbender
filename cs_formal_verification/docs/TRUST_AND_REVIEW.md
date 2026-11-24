# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
The kernel checks proofs about emitted objects. It does not establish that those
objects faithfully represent Rust artifacts or express the intended system claim.
[Verification status](VERIFICATION_STATUS.md) lists every claim and every open item.

The claims cover the constraint description shared by the cached and no-cache circuit JSON files.
Their constraint sections are identical. Only the compiled GKR layers can differ.
Individual circuit statements use the no-cache files. The cached captures use the same proved parser.
Native CPU and worker gates, source placement and exact public lookups imply the complete row constraints.
Cryptographic argument soundness remains open.

The unified RAM outputs reduce to the source read and write tokens.

## Review entry points

The [directory review guide](../lean/human/Human/README.md) separates
[individual circuits](../lean/human/Human/Circuits/README.md) from
[whole-trace execution](../lean/human/Human/Trace/README.md). Subdirectory READMEs
identify the local claim, relevant helpers and scope boundaries.

Start with [the property definitions](../lean/human/Human/Helpers/Properties.lean).
They depend only on [CleanCore](../lean/human/CleanCore.lean), our transcription of Clean, and state soundness,
completeness and the circuit relation.
The helper topics are `Core/`, `Decoder/`, `Memory/` and `Context/`; tables,
delegation and unified-machine context retain their own groups.

For individual circuit soundness, start with its `Circuits/<family>/` model and
local claim, then shared history inputs,
public initialization,
[accepted native matching](../lean/human/Human/Helpers/Context/Model.lean) and
[the selected row's pre-state](../lean/human/Human/Helpers/Context/RowContext.lean).
The accepted initialized history is still part of these claims; reads and ranges
remain conclusions. Circuit setup definitions live in each family's `Tables/`;
shared range/byte/subword constructions live in `Helpers/Tables/`.

For whole execution, start with the [native machine targets](../lean/human/Human/Compiler/NativeTargets.lean) and
their [boot inputs](../lean/human/Human/Trace/Machine/Model.lean).
[RVSoundness.lean](../lean/human/Human/Trace/RVSoundness.lean) states the CPU-only whole-trace claims. Read it with
the [public boot inputs](../lean/human/Human/Helpers/Context/RVPooledBoundary.lean),
[native matching](../lean/human/Human/Helpers/Context/Model.lean), the
[family registry](../lean/human/Human/Helpers/Context/Registries/Pooled.lean), and
[public decoding](../lean/human/Human/Helpers/Decoder/RVPooledProgram.lean) (`RV.decode` of the ROM image).
[RVExecution.lean](../lean/human/Human/Trace/RVExecution.lean) states the shared `RVRealizes`
conclusion (a run of `RV.run` from the public starting state); [RowEvents.lean](../lean/human/Human/Helpers/Memory/RowEvents.lean)
defines native row events, and [RVHistory.lean](../lean/human/Human/Helpers/Memory/RVHistory.lean) executes them on an `RV.State`.
The reference itself, [RV32.lean](../lean/human/Human/ISA/RV32.lean), is part of what is reviewed; its link to Sail is
the [equivalence leaf](../lean/human/Human/ISA/Sail/Theorems.lean).

`Circuits/` owns row references, artifacts, named mappings and local assumptions.
`Helpers/` owns the shared context; `Trace/` owns instruction execution, terminal
realization and composition. The helper import graph is independent of `Trace/`.
No circuit or helper module, in `Human/` or `Proven/Final/`, depends transitively on a trace module
(checked by the review check). `Proven/` contains supporting
calculations, interfaces, proof assembly and artifact guards. Review `Import/`
separately for fidelity ([import guide](../lean/human/Human/Import/README.md)). Per-circuit `circuitModel` and `InterfaceAssumptions`
remain visible; accepted row membership supplies that row's imported constraints.
Shared initialized history derives bounds, actual reads and preprocessing.
[RowPosition](../lean/human/Human/Helpers/Context/RowContext.lean) (RV: [RVRowPosition](../lean/human/Human/Helpers/Context/RVRowContext.lean))
applies earlier native writes without assuming successful reads or ISA execution.

Unified models and workers retain their own explicit public contracts. For their
claims and remaining scope, use the status table rather than inferring whole-machine
coverage from a local operation theorem.

## Checked scope boundaries

These fixtures mark the scope of the current claims (the last row records how the spec treats the case its fixture exercises). They concern the
shared constraint descriptions and logical matching; they do not establish a
whole-system or cryptographic exploit. Keep their public inputs and scope visible
when reviewing or strengthening a theorem.

| Boundary | Checked fixture and consequence |
| --- | --- |
| Inactive padding | [Inactive ADD/SUB row](../lean/test/Tests/InactiveRow.lean): execute zero alone implies neither a PC stutter nor a zero discarded result (the fixture's result column is 123) under the retained local constraints. Padding neutrality needs global state/write obligations; the selected trace model includes active rows. |
| Unissued workers | [Zero-clock rejection](../lean/test/Tests/DelegationZeroInvocation.lean): the circuit's timestamp query 0 rejects an active zero-clock worker in every family (`active_zero_invocation_rejected`). The caller claims do not rely on this: they classify zero-clock workers as unissued and keep their effects in the prefix. |
| Bigint controls | [Bigint control fixture](../lean/test/Tests/UnifiedDelegation.lean): the imported bigint constraints accept a worker row with x12 = 0 and every control bit clear and one with x12 = 65537 (both limbs 1) and only the ADD bit set. The pinned [Rust reference](../../riscv_transpiler/src/vm/delegations/bigint.rs) asserts a control mask below 256 and exactly one bit set besides carry, so it rejects both. The caller-cycle claims keep the worker ABI explicit; full custom-CSR ABI remains open. |
| Worker pointers into low memory | [COPY row](../lean/test/Tests/DelegationROMBoundary.lean): a supported bigint COPY row satisfies the imported constraints and its state port addresses RAM cell 0, a native ROM-shadow address (`worker_accesses_rom`). The spec treats such cells as shadow RAM (`RV.State.delegationRAM`): delegations read and write them, and no load or fetch sees them. |

## Sources and pins

| Component | Source and review obligation |
| --- | --- |
| Lean kernel and standard axioms | Accepted proof-checking foundation. The [axiom audit](../lean/test/Checks/Axioms.lean) records actual dependencies. |
| Lean / Mathlib | `v4.35.0`, pinned in `lean-toolchain` and [lakefile.toml](../lean/lakefile.toml). |
| Clean | tag `v4.35.0`, `b41c196b10cf0f389d2badf5e19e1435e78e6d98`, built from source (`LAKE_NO_CACHE=1`); upstream definitions in `lean/.lake/packages/Clean`. [CleanCore](../lean/human/CleanCore.lean) transcribes the definitions the spec uses, and [its equivalence with Clean](../lean/human/CleanCore/Equivalence.lean) (built by [verify.sh](../verify.sh)) proves each equal to Clean's and lists the deviations. Review the transcription and the deviations; Lean checks proof terms. Within `human/` only that equivalence leaf imports Clean, so Clean, and with it its native_decide prime instances in Clean's Utils/Primes.lean (`lean/.lake/packages/Clean/Clean/Utils/Primes.lean`), is not in the spec's import closure. The proofs in `proven/` do not import Clean either; outside the spec only the audit file [Axioms.lean](../lean/test/Checks/Axioms.lean) imports it (Clean.Specs.Keccak256). |
| Sail model/compiler (equivalence leaf only) | The official sail-riscv model `6136f84` (tag `2026-10-12-6136f84`) compiled by Sail `2ba3212` (0.20.3) with the [airbender-base config](../sail/config/airbender-base.json); pins and their rationale in [PINS.md](../sail/PINS.md), generation in [regen.sh](../sail/regen.sh). The generated model is committed with provenance and BSD licence notices. CI regenerates it and checks the diff. Only [Configuration.lean](../lean/human/Human/Helpers/Core/Configuration.lean), the [Human/ISA/Sail](../lean/human/Human/ISA/Sail/Theorems.lean) modules and the Human library root import it, directly or through other modules; no circuit claim does. `sailModules` in [Trust.lean](../lean/human/Human/Trust.lean) lists these modules, `sailImportEdges` lists the direct imports of the model from `human/` and `proven/`, and [the import check](../lean/scripts/check_import_closure.py) requires both lists to be exact. |
| Sail runtime | `lean-sail` revision `c816ea7ad03cce98d51acee252540fd4215fede8`, fetched by [fetch-lean-sail.sh](../sail/fetch-lean-sail.sh) with the Lean 4.35 [patch](../sail/patches/lean-sail-lean4.35.0.patch) and the [`skip_inductive_codegen` patch](../sail/patches/lean-sail-skip-inductive-codegen.patch): a command wrapper, put before the generated `instruction` type by `regen.sh`, that skips the runtime layout of constructors whose tag exceeds Lean 4.35's limit (lean4#8930). It changes only the compiler; the declarations the kernel checks are unchanged. The claims run the model with `runSail`; [Interpreter.lean](../lean/human/Human/ISA/Sail/Interpreter.lean) carries every successful `runSail` run and every finite machine run to the runtime's `interpretSailEffects`. |
| Platform support | The full model implements the platform hooks concretely; three upstream hooks without a Lean body get trivial bodies in [sail-riscv-lean-missing-externs.patch](../sail/patches/sail-riscv-lean-missing-externs.patch). Experimental extensions and CLINT/interrupt devices are off in [airbender-base.json](../sail/config/airbender-base.json). |
| Project profile/custom reference | Unmodified [00-master.md](airbender/00-master.md) at `2331d1c511f26c17be85879fbab02ab109aefd05`, with [hash/provenance](airbender/provenance.json); the spec's ISA table and decoder pins are named in [RV32.lean](../lean/human/Human/ISA/RV32.lean). Applicability to the circuit revision remains a review obligation. |
| Base ADD/SUB artifact | Frozen PR #585 tip `9501f1f45f075b61389bb301de697514bb61bed8`; [retained no-cache JSON](../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json), SHA-256 `e5aadac65c19335d5adf39b24afad8fca54ca404305058a190004177b325fc49`. Other family JSON paths remain in their reviewed artifact declarations. |

## Import and generation fidelity

CleanCore (Clean's definitions, transcribed) supplies `Expression`, `FlatOperation`, `Environment`, static tables and
`ConstraintsHoldFlat` directly. The [import guide](../lean/human/Human/Import/README.md) lists what to read.

- **Trusted (not kernel-checked):** [Transcribe](../lean/human/Human/Import/Transcribe.lean) and
  [TranscribeCommand](../lean/human/Human/Import/TranscribeCommand.lean), headed `TRUSTED: review`.
  [Trust.lean](../lean/human/Human/Trust.lean) lists allowed external roots and tactic modules, and the spec modules
  that define commands which add declarations (`declarationCommandModules`; review their code as specification);
  [the source check](../lean/scripts/check_trusted_code.py) requires both lists to be exact. The import_circuit command
  reads a circuit JSON, parses it with `Json.parse`, decodes the value with `Circuit.decode` and reflects the result as
  `importedCircuit` (derived `ToExpr`), next to the file's text `importedCircuitSourceBytes`. The 14 cached captures
  use the shared form: it emits no text, adds the placement array and each gate or cache array with more than 253
  entries as a separate constant, and replaces the equal subterms of the reflected circuit with these constants.
  Trusted: the file read, the composition, the reflection and this replacement. `StandaloneBytesClaim` has the kernel
  parse and decode the bytes of the no-cache inits/teardowns file in the plain form. `SharedBytesClaim` does the same
  for the cached inits/teardowns file in the shared form, the only cached file small enough for the module budget.
  For these imports only the file read stays trusted. The sha256 pins of the JSON files, and
  that each circuit and setup JSON is in its canonical form, are checked by
  [check_circuit_json.py](../lean/check_circuit_json.py) (verify.sh step 1b). In CI,
  [check_compiled_circuits.py](../lean/scripts/check_compiled_circuits.py) runs the Rust generator test of each
  imported circuit JSON and fails on a difference. [check_compiler_captures.py](../lean/scripts/check_compiler_captures.py)
  requires that each setup embeds the imported no-cache circuit of its family.
- **Spot checks:** [ImportSpotChecks.lean](../lean/test/Tests/ImportSpotChecks.lean) has kernel examples that a
  reviewer can repeat with other values. Each example names its JSON file and JSON path. They read one gate
  coefficient, one placement entry and one cached lookup expression of the shared add-sub and chi imports. They decode
  one add-sub word and one word-memory word with Sail and find the native query of each in the decoder table.
- **Proved:** the parser accepts exactly the JSON texts without duplicate member names, and a text has one value
  (`ParseSoundClaim`, `TextUniqueClaim`, [Theorems](../lean/human/Human/Import/Theorems.lean), against the byte-level
  grammar of [JsonGrammar](../lean/human/Human/Import/JsonGrammar.lean): RFC 8259 restricted to integers and to `\u`
  escapes below U+10000); the decoder returns exactly the circuit whose serde JSON (`Serde.encode`,
  [Serde](../lean/human/Human/Import/Serde.lean) and the schema) is the value (`DecodeClaim`). Each artifact's `ArtifactImportClaim` (`StandaloneImportClaim`, `UnifiedImportClaim` for the
  inits/teardowns layouts) states that every imported definition the claims use is the meaning function applied to
  `importedCircuit`; the kernel evaluates both sides.
- **Reviewed as specification:** the meaning, pure functions of the decoded artifact:
  [Columns](../lean/human/Human/Import/Columns.lean) (logical variables, ports, clocks, decoder columns, per-family
  query profiles; `PlacementsClaim` states the placement index), [Operations](../lean/human/Human/Import/Operations.lean)
  (equations and lookups as Clean operations) and
  [InitsTeardownsLayout](../lean/human/Human/Import/InitsTeardownsLayout.lean); the schema with its serde JSON and
  [Coefficients](../lean/human/Human/Import/Coefficients.lean) (the coefficient cast equivalence and the field constants are `ConstantsClaim`).
- **Not reviewed:** `Human/Import/Exec/` (the parser, the decoder, the emitters of the literal terms, and FastColumns, which
  derives copies of the [Columns](../lean/human/Human/Import/Columns.lean) functions with the placement map passed in, for the emitter's speed); each file names
  the claims that fix its behaviour.

Placement guards reject missing or ambiguous logical variables and check memory/witness banks. Named imported
descriptors do not prove that Rust preprocessing or decoder-table contents match the model.

Setup tables (`artifacts/setup/*.json`) are parsed by the same `Json.parse` and read by
[SetupEmit](../lean/human/Human/Import/SetupEmit.lean) (trusted, headed `TRUSTED: review`) into the blocks of
[SetupBlocks](../lean/human/Human/Import/SetupBlocks.lean). The JSON reader (`parseSetup`) is the trusted step, as
the file read and the reflection are for circuits. The import emits the JSON blocks as they are. Kernel claims make
each table definition of the bigint, G, Keccak, shift/byte, add/sub, jump/branch, multiply/divide, word, subword and
unified setups equal to the imported rows on the complete trace domain, the range columns of the CPU setups equal to
their formulas, and the public worker tables equal to the imported worker data with their range columns. The CPU
claims state the public generic rows (`NativePublicSetup.genericRow`) of the setup fixture program: its initial state
and its program image (`rvMachineProgramImage`). The BLAKE2 round table reads the imported rows, and
`Blake2Round.SetupImportClaim` makes them equal to the round row formulas; the three split Keccak tables read their
imported rows too, and `Keccak.Split.ColumnParity.SetupImportClaim`, `Keccak.Split.ThetaRho.SetupImportClaim` and
`Keccak.Split.Chi5.SetupImportClaim` make them equal to their row formulas. The claim modules import the raw setup data; the
definitions that the machine claims use do not, except the round and split Keccak tables, which read their imported
rows. `test/Tests/ImportSetupSpotChecks.lean` checks single imported values
against the JSON. See [the setup README](../lean/artifacts/setup/README.md).

## What CI re-checks

`.github/workflows/ci.yml` calls the reusable `.github/workflows/lean-formal-verification.yml`.
The `pr-checks` job requires its result. The Lean job starts for every PR. It exits with success when no input changed.
Manual dispatch of `ci.yml` selects incremental, cold or kernel replay on the selected branch.
Schedules start from the default branch after the workflow is merged.
The reusable workflow runs [verify.sh](../verify.sh) in two modes, and separately a
kernel replay ([ci/README.md](../ci/README.md)). A local `./verify.sh` is the cold mode.

| | incremental (pull requests) | cold (pushes to protected branches, nightly) |
|---|---|---|
| build | Lake rebuilds what changed since the restored build of an earlier commit; unchanged modules are its `.olean` files | everything elaborated again (only the toolchain, the dependency checkouts, Mathlib's published `.olean` files and the generated Sail model are restored) |
| axiom audits | read from Lake's build log of the audit modules (`VERIFY_AUDITS=replay`): the messages recorded when those `.olean` files were built, the same trust as the files themselves | `lake env lean` elaborates each audit file again (`fresh`) |
| every `#print axioms` answered, standard axioms only | yes | yes |
| regressions, test executable, JSON pins, guide links | yes | yes |
| final proof and separate non-vacuity coverage for every public claim, and a checked application of each claim with premises to its witness | yes | yes |
| review check's Lean inventory (audit roots, guide names) | skipped when its inputs (guides, audit file, Lake input hashes of the claim modules) equal those of a passing check recorded in the build | yes |
| module budget | ledger of earlier measurements by input hash, plus the modules built now | every module measured in this run |

An incremental run trusts the restored build (produced by an earlier CI run of this repository). Cold runs re-derive the project modules from source. Schedules are active only after the workflow reaches the default branch.

**Kernel replay** (job `kernel_replay`, nightly, or manually; `backup-check.sh` by hand):
`lake check` exports the default targets with everything they import. Lean's kernel must accept every declaration,
and the export axiom audit must find only the standard axioms. Native `leanchecker-paranoid` must accept the same retained export. `leanchecker` also replays the two modules it leaves out (`human/CleanCore/Equivalence.lean`,
`test/Checks/Axioms.lean`: they import Clean's `native_decide` prime instances). This catches an `.olean` whose
declarations the elaborator accepted but Lean's kernel would not. A separate `lake check --paranoid` step reports
the bundled external checkers. Those results are advisory and do not fail the job. The replay does not run on pull requests or in the cold runs.
The job runs on the runner host, where `bwrap` can create `lake check`'s sandbox; if it cannot, the job replays with
`leanchecker` only and fails.

## Modeled tables and logical arguments

[Range.lean](../lean/human/Human/Helpers/Tables/Range.lean) defines the 16-bit and 19-bit tables.
The worker setup claim makes the imported 16-bit and timestamp range columns of each worker equal to the increasing
prefix and zero padding; `Range13ImportClaim` binds the 13-bit table to table 26 of the multiply/divide setup.
The [setup inventory](../lean/artifacts/setup/README.md) lists all 16 exported setups and their claims.
Fresh Rust exports and content pins check the current input bytes. No theorem verifies the Rust setup generator.

The bigint, G, Keccak, shift/byte and CPU table definitions are mathematical row formulas. Kernel claims make each
formula equal to the imported native rows.

`Accepted` checks imported equations/lookups and logical native state/memory
permutations. Decoder membership and caller/request matching are likewise logical
conditions; cryptographic enforcement of any of them is outside the claims.

The [native worker certificates](../lean/human/Human/Compiler/WorkerCertificates.lean)
describe both submitted worker pools exactly, in order. The target proofs derive every row constraint from the
native cached gates, source placement, public worker lookups and participation.
The [worker certificate proofs](../lean/proven/Proven/Final/Compiler/WorkerCertificates.lean)
include a full active witness for each of the six worker circuits used by the targets.
The constraint-description targets retain worker constraints as premises.

The [public setup interpretation](../lean/human/Human/Compiler/NativePublicSetup.lean) indexes decoder rows by PC.
Unsupported slots retain their minus-one payload. Tagged circuits retain their native discriminator and zero tail padding.
ADD/SUB retains minus-one tail padding. The public bound fixes capacity, selector bounds and omitted zero coordinates.
Zero-mask LW and LHU rows retain a nonzero destination. The decoder-membership proofs use these fields to reject padding rows.

The [decoder comparison](../lean/scripts/check_program_decoder_rows.py) compares the compiled Lean row function with native exports.
It also compares circuit objects across public programs and the shared unrolled profiles.
The Lean oracle checks the mask and omitted-field conditions for every projected entry before it selects a circuit family.
The Python checker checks these conditions for each emitted row. The tests include the public ZKsync OS text and
loads and MUL into x0 on all three machine profiles. Full uses ADD NOP rows for these x0 forms.
Reduced and unified use an ADD NOP row for LW into x0 and sentinel rows for LHU, LB and MUL into x0.
Each test binds the Lean model to the tested Rust preprocessing result.
These tests do not prove Rust decoder equivalence for every possible program.

Caller and worker claims add public inputs, all visible in their `…Inputs` structures:
- Request matching derives exact worker/caller multiplicity, unique native slots, full CSR families and the placement of
  each issued worker inside its caller's four-tick cycle (invocation at start + 1, writes at start + 3). Machine ports
  include native offset zero; Clean event clocks add one. Zero-clock workers are classified as unissued and keep their
  effects in the actual prefix.
- Caller windows (`Caller.rv_request_window_soundness`, `Caller.rv_mixed_window_soundness` and the hash-window claims)
  cut at aligned instruction boundaries after clock two and derive the cut states, boundary tokens and retained clocks
  from architectural matching. Worker boundaries are projected from shared matching; x0 refreshes are no-ops.
  Public mode/count, span duration, modeled tables and (for hash spans) the span-size ABI remain explicit.
- A complete hash span's final state is the spec's run of its delegation calls (`HashSpan.RVResult`, up to the PC
  advance). Prepared spans ([prepared hash windows](../lean/human/Human/Trace/UnifiedReduced/RVPreparedHashWindows.lean),
  [prepared round windows](../lean/human/Human/Trace/UnifiedReduced/RVPreparedRoundWindows.lean)) derive the control at
  each cut from a public ADDI-from-x0/LUI preparation registry
  ([RVControlPreparation](../lean/human/Human/Helpers/UnifiedReduced/RVControlPreparation.lean)); the final
  preparation cycle must be worker-free, earlier worker effects stay in the history, and the extended-BLAKE masks are
  derived from raw matching inside each public controller region, which must cover every extended-round worker.
  Public preparation, mode/count/duration, cut order and alignment remain inputs; general acceptance is not shown to
  run valid protocols.
- `RVProgramCallerRegion` and `RVProgramProtocolWindowInputs` replace the selected worker family and count by a public
  PC/clock interval of CSR entries (a sequential ordinary registry excludes ordinary code from it); matching derives the
  family, counts and slots. The machine targets compose whole runs with callers. The valid-use claims cover valid
  calls, and invalid calls follow the circuit (`ISA/Delegations.lean`).
- Caller cycles (`Caller.rv_caller_cycles_soundness`, `Caller.rv_prepared_round_cycles_soundness`) bind each caller's
  fetch, its matched worker's port reads/writes and the PC advance in one history. They carry no code-domain premise:
  the ROM image is separate from RAM and the RV table's fetch guard keeps entries in aligned ROM words. Both bigint control
  gaps above remain admitted, and the worker ABI stays explicit.

Native columns retain full address/time/value limbs, including readonly
clock refreshes. Bounds, latest-write reads and Clean online-consistent histories
are derived from those relations and public initialization. Retiming introduces
initialization writes and preserves addresses/values; it does not prove cryptographic
permutation or lookup enforcement. Prover/verifier refinement and protocol soundness
are separate obligations.

## Public state, profiles and external inputs

[InitialImageRV.lean](../lean/human/Human/Helpers/Memory/InitialImageRV.lean) reads the public `RV.State`'s registers
(x0 as 0) and RAM words over a distinct public cell domain; a cell outside `RV.readable` fails. Public inputs
bind the initial PC/clock, program bytes (the ROM image) and the modeled ROM tables. The memory claims keep the
alignment and domain conditions of their input records; the RV claims have no machine-configuration, Sail memory-map or
code-domain premise. Per-row expected reads, operand bounds and execution results are conclusions.

The boot profile starts at PC zero with zero registers. The RAM seeds are the Init tokens of the inits/teardowns
circuit (`RVPooledBootInputs`), and `BootRamZeroClaim` derives that every tracked RAM cell of the starting state reads
0, shadow RAM below 4 MiB included. Residual items, not derived from a circuit: the register seeds (the chunk's public
state), RAM coverage (only cells of initialized windows are tracked) and cross-chunk clock chaining; see
[State.lean](../lean/human/Human/ISA/State.lean). The spec keeps the ROM image (`rom`: fetch and loads below `ROM_END`)
apart from RAM (`mem`), whose cells below `ROM_END` are shadow RAM that only delegations reach.
[Native ROM view](../lean/human/Human/Helpers/Memory/Native.lean) names the zero native shadow slots. Slot masking
comes from `mask_read_for_witness` in `riscv_transpiler/src/replayer/mod.rs`;
zero seeds come from `inits_or_teardowns_as_flattened_relation` in
`prover/src/gkr/prover/forward_loop/utils.rs`. The modeled word-ROM and subword tables are built from the ROM image
(`romImageRV`, `ROM.wordsRV`), not from the seed values. Rust fidelity and cryptographic enforcement remain external.

A load into x0 is a no-op that only advances the PC in `RV.exec` (Airbender's rule), so the claims need no
load restriction. Likewise `RV.step` has no next state for misaligned accesses, stores into ROM, misaligned jump
targets and fetches outside ROM; a claim that concludes a step therefore also concludes these conditions.

The jump/branch/SLT claims take the terminal PC as a canonical word (`terminalPC` in `RVInterfaceAssumptions` and
`RVPooledBootInputs`, `terminalCanonical` in the jump family's `RVExecutionInputs`): the circuit does not range-check
the outgoing PC's high limb, so the last row's target is bounded only through it. Binding it to the teardown circuit is open.

[RVExternalInput.lean](../lean/human/Human/Helpers/Decoder/RVExternalInput.lean) gives the CSR 0x7C0 forms. The stream
is `RV.State.input`, independent of the witness. `StreamPorts` explicitly connects native
response ports; the circuit does not authenticate a fixed stream and permits
different responses. Native clocks derive positions, and the execution claim
concludes the exact consumed count. Hints consume no word and make no application
I/O claim.

The selected claims retain normal-path, field and terminal boundaries.
The checked unissued-worker and bigint-control fixtures must stay
visible at their actual logical scope; no whole-system exploit, circuit fix or
assumed ABI validity follows. Use [Verification status](VERIFICATION_STATUS.md)
for the fixtures and every open item.
