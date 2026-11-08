# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
The kernel checks proofs about emitted objects. It does not establish that those
objects faithfully represent Rust artifacts or express the intended system claim.
[Verification status](VERIFICATION_STATUS.md) is the coverage and gap inventory;
[the plan](FORMAL_VERIFICATION_PLAN.md) contains pending work.

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

For whole execution, start with [RVSoundness.lean](../lean/human/Human/Trace/RVSoundness.lean), then
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
No circuit or helper module, in `Human/` or `Slop/Final/`, depends transitively on a trace module
(checked by the review check). `Slop/` contains supporting
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
imported richer relations and logical matching; they do not establish a
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
| Lean / Mathlib | `v4.34.1`, pinned in `lean-toolchain` and [lakefile.toml](../lean/lakefile.toml). |
| Clean | tag `v4.33.1`, `93c9d1ef45be9f687214625d7857889cf2485504` (builds unchanged on Lean `v4.34.1`); upstream definitions in `lean/.lake/packages/Clean`. [CleanCore](../lean/human/CleanCore.lean) transcribes the definitions the spec uses, and [its equivalence with Clean](../lean/human/CleanCore/Equivalence.lean) (built by [verify.sh](../verify.sh)) proves each equal to Clean's and lists the deviations. Review the transcription and the deviations; Lean checks proof terms. Within `human/` only that equivalence leaf imports Clean, so Clean, and with it its native_decide prime instances in Clean's Utils/Primes.lean (`lean/.lake/packages/Clean/Clean/Utils/Primes.lean`), is not in the spec's import closure. The proofs in `slop/` do not import Clean either; outside the spec only the audit file [Axioms.lean](../lean/test/Checks/Axioms.lean) imports it (Clean.Specs.Keccak256). |
| Sail model/compiler (equivalence leaf only) | The official sail-riscv model `6136f84` (tag `2026-10-12-6136f84`) compiled by Sail `2ba3212` (0.20.3) with the [airbender-base config](../sail/config/airbender-base.json); pins and their rationale in [PINS.md](../sail/PINS.md), generation in [regen.sh](../sail/regen.sh). The generated model is not committed. Only [Human/ISA/Sail](../lean/human/Human/ISA/Sail/Theorems.lean) and [Configuration.lean](../lean/human/Human/Helpers/Core/Configuration.lean) import it; no circuit claim does. |
| Sail runtime | `lean-sail` revision `c816ea7ad03cce98d51acee252540fd4215fede8`, fetched by [fetch-lean-sail.sh](../sail/fetch-lean-sail.sh) with the Lean 4.34 [patch](../sail/patches/lean-sail-lean4.34.1.patch). |
| Platform support | The full model implements the platform hooks concretely; three upstream hooks without a Lean body get trivial bodies in [sail-riscv-lean-missing-externs.patch](../sail/patches/sail-riscv-lean-missing-externs.patch). Experimental extensions and CLINT/interrupt devices are off in [airbender-base.json](../sail/config/airbender-base.json). |
| Project profile/custom reference | Unmodified [00-master.md](airbender/00-master.md) at `2331d1c511f26c17be85879fbab02ab109aefd05`, with [hash/provenance](airbender/provenance.json); the spec's ISA table and decoder pins are named in [RV32.lean](../lean/human/Human/ISA/RV32.lean). Applicability to the circuit revision remains a review obligation. |
| Base ADD/SUB artifact | `av_gkr_compiler` revision `28ffe3ff0353edd9051485c2974b28b52b495dc4`; [retained no-cache JSON](../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json), SHA-256 `084a58f08dd122160b548689383f74d4a790c782046f8a5bf43f9f287c22a620`. Other family JSON paths remain in their reviewed artifact declarations. |

## Import and generation fidelity

CleanCore (Clean's definitions, transcribed) supplies `Expression`, `FlatOperation`, `Environment`, static tables and
`ConstraintsHoldFlat` directly. The [import guide](../lean/human/Human/Import/README.md) lists what to read.

- **Trusted (not kernel-checked):** [Transcribe](../lean/human/Human/Import/Transcribe.lean) and
  [TranscribeCommand](../lean/human/Human/Import/TranscribeCommand.lean), headed `TRUSTED: review`. The import_circuit command
  reads a circuit JSON, parses it with `Json.parse`, decodes the value with the `FromJson` instances derived for the
  serde mirror ([Schema](../lean/human/Human/Import/Schema.lean)) and reflects the result as `importedCircuit`
  (derived `ToExpr`), next to the file's text `importedCircuitSourceBytes`. The sha256 pins of the JSON files are
  checked by [check_circuit_json.py](../lean/check_circuit_json.py) (verify.sh step 1b).
- **Proved:** the parser accepts exactly the JSON texts without duplicate member names, and a text has one value
  (`ParseSoundClaim`, `TextUniqueClaim`, [Theorems](../lean/human/Human/Import/Theorems.lean), against the byte-level
  grammar of [JsonGrammar](../lean/human/Human/Import/JsonGrammar.lean): RFC 8259 restricted to integers and to `\u`
  escapes below U+10000). Each artifact's `ArtifactImportClaim` (`StandaloneImportClaim`, `UnifiedImportClaim` for the
  inits/teardowns layouts) states that every imported definition the claims use is the meaning function applied to
  `importedCircuit`; the kernel evaluates both sides.
- **Reviewed as specification:** the meaning, pure functions of the decoded artifact:
  [Columns](../lean/human/Human/Import/Columns.lean) (logical variables, ports, clocks, decoder columns, per-family
  query profiles; `PlacementsClaim` states the placement index), [Operations](../lean/human/Human/Import/Operations.lean)
  (equations and lookups as Clean operations) and
  [InitsTeardownsLayout](../lean/human/Human/Import/InitsTeardownsLayout.lean); the schema and
  [Coefficients](../lean/human/Human/Import/Coefficients.lean) (coefficient cast equivalence proved).
- **Not reviewed:** `Human/Import/Exec/` (the parser and the emitters of the literal terms); each file names the claims
  that fix its behaviour.

Placement guards reject missing or ambiguous logical variables and check memory/witness banks. Named imported
descriptors do not prove that Rust preprocessing or decoder-table contents match the model.

Setup tables (`artifacts/setup/*.json`) are parsed by the same `Json.parse` and read by
[SetupEmit](../lean/human/Human/Import/SetupEmit.lean) (trusted, headed `TRUSTED: review`) into the blocks of
[SetupBlocks](../lean/human/Human/Import/SetupBlocks.lean). Besides transcribing the JSON,
the import replaces each recognised table region (table ids in `gridCatalogue`) by a
`grid` block, a named row formula, after comparing every row of the region with the JSON;
any mismatch fails the import. This comparison is an elaborator responsibility with the same
trust as the transcription: it is elaborator code, not kernel-checked, and the kernel proofs
see only the formula. See [the setup README](../lean/artifacts/setup/README.md).

The target remains the richer no-cache representation. Compiled-gate implication,
witness extension and cached-layout equivalence are unproved. Generic prime-field
claims retain their stated minimum moduli and inverse compatibility; they do not
establish import of the native Proth120 artifact with its own coefficients.

The reference is our own RV32 spec ([RV32.lean](../lean/human/Human/ISA/RV32.lean),
[State.lean](../lean/human/Human/ISA/State.lean), [Delegations.lean](../lean/human/Human/ISA/Delegations.lean)); review
it as a specification. Its link to the official Sail model is the
[equivalence leaf](../lean/human/Human/ISA/Sail/Theorems.lean) (`DecodeIsSailClaim`, `StepIsAirbenderClaim`,
`MachineChecksClaim`; proofs in `slop/Slop/ISA/Equiv/`). Review [regen.sh](../sail/regen.sh),
[PINS.md](../sail/PINS.md) and the configuration copy only for that leaf: generation fidelity (Sail compiler to
Lean) is trusted, not proved; the model is the official sail-riscv source compiled without pruning. The equivalence
is stated against the Airbender machine of [Airbender.lean](../lean/human/Human/ISA/Sail/Airbender.lean) (Sail's execute
plus the listed changes, on a fixed configuration: misa, memory map, reset state), so what it shows is only as good
as that list.

Public program tables are built from the ROM image by `RV.read` and `RV.decode`
([RVProgram](../lean/human/Human/Helpers/Decoder/RVProgram.lean)); the native metadata projection of an `RV.Instr`
still needs review against Rust (`add_sub_family/decoder.rs`, `riscv_transpiler/src/ir/simple_instruction_set.rs`).
Custom CSR/Zimop behavior is in the spec: the CSR 0x7C0 input read/write forms and the delegation calls are the
only CSR forms with a next state.

## Modeled tables and logical arguments

[RangeChecks.lean](../lean/human/Human/Helpers/Tables/Range.lean) enumerates 16-bit limbs using
Clean's `StaticTable`; membership characterization is kernel checked. Its rows
reconstruct [Rust range setup](../../prover/src/gkr/virtual_polys/range_check.rs),
selected with 16 bits in [the prover](../../prover/src/gkr/prover/mod.rs).
The 19-bit timestamp table and worker controller/XOR/operation tables have the
same unproved setup-generator correspondence. Exact extracted rows, table identity,
query binding and padding remain deferred provenance work.

`Accepted` checks imported equations/lookups and logical native state/memory
permutations. Decoder membership and caller/request matching are likewise logical
conditions; cryptographic enforcement of any of them is outside the claims.

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
  family, counts and slots. General protocol validity, invalid-call ABI and whole caller retirement remain open.
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

The jump/branch/SLT claims take the terminal PC as a canonical word (`terminalPC` in `RVTraceInputs` and
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
for the fixtures and all unresolved coverage, and
[the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones) for downstream proofs.
