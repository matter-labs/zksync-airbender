# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
A proof does not establish that its definitions express the intended claim or
that an imported object faithfully represents the source artifact.

## Origin and status

| Component | Origin | What needs checking |
| --- | --- | --- |
| Lean kernel and standard axioms | Reused foundation | Accepted proof-checking foundation |
| Mathlib and Clean | Pinned upstream dependencies in `.lake/packages` | Definitions must fit their use; their proof terms are checked by Lean |
| Clean compatibility preparation | Our `scripts/prepare_clean.py` | Original source hashes guard Lean 4.31 tactic-import, factory-registration and proof-reduction patches. Semantics, algorithms and theorem statements are unchanged; repaired proof terms are kernel-checked and axiom-audited. Review the explicit patch list. |
| Sail instruction semantics and runtime | Upstream source in `vendor/sail-riscv` and pinned `lean-sail` dependency | Selected configuration and our architectural projection |
| Project profile and custom-operation specification | Unmodified source in `vendor/airbender`, with revision/hash | Meaning of custom operations and applicability to this circuit revision |
| Generated Sail Lean model | `generated/sail-rv32` | Compiler/pruning fidelity is not proved; a recorded header parameterizes missing platform externals without changing instruction bodies |
| Sail platform support | Our `scripts/SailPlatform.lean`, copied by the original backend | Experimental extensions disabled, matching the pinned emulator default/getter; runtime-error compatibility is proved in `Proofs/Sail/Runtime.lean`; terminal/reservation calls are abstract parameters, not implementations |
| Properties, mappings, contracts, Sail interface and public claims | Our `Airbender/Review` code | Human review of intended meaning and scope |
| JSON parser, coefficient conversion, emitter | Our `Airbender/Import` code | Faithful import/emission is not proved; coefficient cast equivalence is proved |
| Algebra, Sail support and circuit proofs | Our `Airbender/Proofs` code | Lean checks the proof terms; routine review starts with the public claims |

Clean directly supplies the expression and constraint semantics. Our source-format
JSON schema is parser data, not a second arithmetic model. There is no local
expression evaluator or equivalence bridge to Clean. The 16-bit table in
[RangeChecks.lean](Airbender/Review/RangeChecks.lean) enumerates all limbs through
Clean's `StaticTable`; its membership characterization is kernel checked.
Its rows are a handwritten reconstruction of [Airbender's range setup generator](../../prover/src/gkr/virtual_polys/range_check.rs),
selected with 16 bits in [the prover](../../prover/src/gkr/prover/mod.rs).
That reconstruction and the importer's binding of range queries to it require review;
their correspondence with the Rust setup is not proved.
Generated-table extraction is a deferred task in [the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

The [clock claims](Airbender/Review/Trace/Theorems.lean) use eight timestamp
queries and placement-resolved state/port columns imported from each selected
JSON. The 19-bit range table retains the same setup-provenance boundary.
The shared `clocks` claim derives all per-row clock bounds/alignment from
`Accepted`'s logical native tuple matching and `ClockBoundary`'s public initial
clock conditions. Matching is built from imported row columns; its cryptographic
enforcement is external. Clean's `SourceSinkPath` supplies the state path; checked
strict-clock and flow lemmas show it includes every transition and that access
times are unique. Selected normal-path traces now establish actual intermediate Sail execution
and terminal PC/cell reads under the explicit public boundary and separate
`NoDiscardedLoads` restriction. The [discarded-load test](Tests/DiscardedLoad.lean)
proves that restriction cannot be dropped from the current sparse-memory model:
native NOP acceptance can coexist with an actual Sail memory error. The pinned
[Airbender profile](vendor/airbender/00-master.md) initializes RAM and GPRs to zero;
our current boundary accepts more general public states. The same profile
explicitly makes loads to x0 PC-only NOPs, even for unaligned addresses. The
unchanged Sail theorem therefore retains the exclusion. The explicit `profileClause` adapter now implements that documented deviation
with Sail's ADDI x0,x0,0 clause; `airbender_soundness` covers it using the same
trace proof. This adapter is our reviewable profile connection, not an upstream
Sail LOAD claim. The [initialization profile](Airbender/Review/Trace/Initialization.lean) states zero GPR/non-ROM RAM and PC=0. [NativeMemory](Airbender/Review/Trace/NativeMemory.lean) separates zero-valued native ROM slots from public code bytes: `NativeBootBoundary` binds the raw seed and modeled ROM table to those independent inputs. `native_boot_soundness` reuses the physical Sail trace proof through a kernel-checked view conversion. It changes only unused ROM-read values, preserving imported constraints, decoder queries, addresses, timestamps, outputs and logical matching. Registers/non-ROM RAM retain their exact values; ROM reads retain public bytes. Missing image cells fail. The native slot masking comes from `riscv_transpiler/src/replayer/mod.rs` (`mask_read_for_witness`); zero seed components come from `prover/src/gkr/prover/forward_loop/utils.rs` (`inits_or_teardowns_as_flattened_relation`). Rust implementation fidelity and cryptographic enforcement remain external.
Register/RAM ports in [Trace/MemoryPorts.lean](Airbender/Review/Trace/MemoryPorts.lean)
are emitted from the same JSON, including address-space polarity and old/new
values. Native matching and decreasing prior-write times prove every access
address originates in the initial memory image. With one initial cell per address,
`memory_paths` covers every access in strictly increasing time and joins adjacent
accesses through the exact address/time/value token. `latest_reads` proves that
no intervening write is skipped. `cell_histories` establishes Clean's actual
online-consistency relation for every address, using exactly its native accesses
plus an explicit initialization write. Real access times are shifted by one to
reserve time zero for each cell's initialization. The global `memory_history`
composes these into one Clean history: initialized addresses receive distinct
earlier timestamps, then every native timestamp receives the same offset.
The retiming proof changes no address or value and preserves Clean consistency.
`read_bounds` and `terminal_bounds` propagate 16-bit limbs from
the public initial image and program-table ranges through native matching and
the imported arithmetic/word-memory writes. The small
[value boundary](Airbender/Review/Trace/Values.lean) describes only those public
inputs, including the disabled-ROM row's zero outputs.
[InitialImage.lean](Airbender/Review/Trace/InitialImage.lean) constructs initial
cells from actual Sail reads over a public address domain. Its successful-result
equality binds the trace's initial cells; bounds, zero clocks and address uniqueness
are proved. Missing cells fail instead of receiving invented values.
Selected normal-path traces now establish actual intermediate Sail execution
and terminal PC/cell reads under the explicit public boundary.
The same module's `initialState` binds the native initial PC to Sail's accessor.
`pc_bounds` uses that binding and native state matching to derive all selected
row/terminal PC ranges; individual initial-PC range assumptions are unnecessary there.
`initialized_cells` binds every imported address to a typed public Sail cell;
`address_bounds` then derives canonical address limbs. Pair coding preserves each
limb, so a noncanonical pair cannot pass by sharing the same combined word value.
Decoder input column metadata is imported from the same JSON and placement map;
the importer checks its memory/witness bank and unique logical variables. These
descriptors alone do not establish decoder table contents or membership.
The generated `encdec_backwards` reuses the original selected-module mappings;
kernel checks cover the seven restricted instructions and both custom CSR encodings. The slice
excludes the postlude's illegal fallback, so only successful restricted decoding
is targeted. [Program.lean](Airbender/Review/Trace/Program.lean) constructs modeled
decoder rows from actual public byte reads and a pure result of that actual decoder
term for the restricted subset. This proves decoding is independent of later
CSR/register state. Unsigned mul/div uses the same module's interpreter-based
constructor: the original M decoder reads public `misa`. Its source evidence
retains the actual successful decoder execution at that configuration; the
checked fixtures reject disabled M. The original decoder frame theorem proves
that successful decoding preserves state and is replayable with the same `misa`;
native histories preserve that configuration. Arbitrary admitted mul/div traces
now compose original fetch/decoding and Sail execution/retirement, from the
unchanged public state to the terminal PC and native cell reads. Both image
constructors supply the same small source record at the current state; the frame
proof transports it through native histories and PC retirement. Each constructor's native
preprocessing projection needs review against the Rust decoder; it defines no
instruction arithmetic. Logical query membership and imported Boolean equations
derive each selector bit, PC correspondence and immediate bounds. The original
Sail instruction is retained even when its native row is preprocessed to NOP.
[NonDeterminism](Airbender/Review/Trace/NonDeterminism.lean) adds the native
CSRRW 0x7C0 metadata projection and explicit custom clause; it does not reuse
standard Sail CSR execution as the custom-operation specification. The pinned Zicsr enable check reduces to
true. Actual fetch, index/immediate queries and all nine selector bits are checked;
native timestamps derive chronological prefix consumption under an explicit,
witness-independent `StreamPorts` input connection. The stream is not
authenticated by the circuit. The shared x0/history proof uses proved metadata
facts for both projections, preserving the same Clean constraint semantics.
Native CSR-read history derives the actual final Sail register value.
The visible `clause` uses native Sail effects for the pinned custom operations
and preserves the existing standard-instruction clauses. Row dispatch and
retirement compose every admitted mixed trace, reaching the terminal cells and
the exact stream counter.
Rust setup fidelity and cryptographic membership enforcement remain external.
[ROM.lean](Airbender/Review/Trace/ROM.lean) builds the current modeled ROM rows
from the same public initial image. Its checked `rom_reads` binding returns actual
Sail bytes for every active query; disabled queries and output ranges are derived.
This proves neither Rust setup extraction nor cryptographic membership enforcement.
Native histories preserve ROM code bytes and transport fetched/decoded source
evidence to later Sail states. The [selected trace claim](Airbender/Review/Trace/Theorems.lean)
composes the family interfaces and actual Sail instruction states. Its
[boundary](Airbender/Review/Trace/Execution.lean) binds public initialization,
modeled ROM, complete GPR/domain/configuration data and public code. Logical
matching/membership remains external. `instructionClause` only dispatches to
original generated clauses; `SailTrace` reuses Mathlib finite relation composition.
The unchanged Sail theorem explicitly excludes LW-to-x0; the Airbender profile
uses its documented NOP rule and covers it. Arithmetic writes to x0 are covered. Full fetch faults/interrupts/exceptions are
outside the normal-path claim.
The internal [Sail word-state proofs](Airbender/Proofs/Sail/WordMemoryState.lean)
normalize the pinned runtime's actual four-byte write and prove readback, disjoint
read preservation, equal-value stuttering and GPR/memory separation. They provide
state-frame machinery. The [virtual word transport proofs](Airbender/Proofs/Sail/VirtualMemory.lean)
compose the original Machine translation, PMA/PMP/MMIO checks and native transfers.
The selected LW/SW transport contract follows from public CSR configuration and
an ordinary aligned effective-address domain; discarded LW addresses still need
trace justification.

The unified [native memory claim](Airbender/Review/UnifiedReduced/Theorems.lean)
connects initialized matching to actual Sail cell reads and writes. Its public
inputs are the starting Sail state/domain, program image, clock boundary and
logical decoder membership. Imported equations and that decoder derive x0
preservation for every admitted selector. No operand bounds or expected reads
are supplied. The [arithmetic model](Airbender/Review/UnifiedReduced/Model.lean)
uses this history for ADD/ADDI/SUB/LUI/AUIPC soundness, keeping named word mappings
and public initialization visible. Only original source-register initialization
remains beyond the shared inputs, so discarded x0 instructions can read their
erased original operands. Local calculation interfaces stay under `Proofs/`.
Retirement for other selectors and pooled setup semantics remain open.

The shared [delegation memory claim](Airbender/Review/Delegation/Theorems.lean)
imports every register/indirect port and timestamp query from all four layouts.
Public Sail initialization and logical matching derive prior-clock/address bounds,
strict per-address order and Clean latest-write/read histories. Caller-clock
alignment remains external until request binding is connected. Operation/frame,
ABI and full hash composition remain separate; this is a logical memory proof.
The shared [operation inputs](Airbender/Review/Delegation/Operations.lean) bind
modeled tables and the remaining extended-round/active-Keccak caller conditions.
`operation_memory_soundness` handles arbitrary family pools and derives every
read/write/terminal word bound through one initialized history.

The bigint [memory interface](Airbender/Review/Bigint/Memory.lean) retains public
Sail initialization, caller-clock alignment and the current modeled table.
Accepted writes preserve all word bounds across every opcode, so history derives
both pointers and all sixteen indirect addresses without range assumptions.
This does not establish the caller ABI or full request/response execution; the
checked no-opcode/high-control mismatch remains flagged.

For BLAKE2 G, start with the [row contract](Airbender/Review/Blake2G/Row.lean)
and `Row.soundness` in [the public claims](Airbender/Review/Blake2G/Theorems.lean).
One assignment connects the controller update, the complete sixteen-word state
update against Clean's `Specs.BLAKE3.g` (shared with BLAKE2s), and six byte addresses.
The ABI domain, four mixing-input bounds, pointer bounds, port reads/writes and
untouched-lane frame are explicit. Alignment and selector bounds/distinctness
are proved. Controller/XOR setup rows remain reconstructions with an unproved
Rust binding; memory descriptors are imported directly from JSON. Import/interpretation
fidelity, cryptographic memory enforcement and complete delegation/hash execution remain
outside the claim. The arithmetic proof uses a kernel-checked sublist of twenty
assertions and eighteen XOR queries from the same artifact; it does not need the
controller or timestamp constraints. The full row claim retains its frame/ABI obligations.
For initialized G-only pools, [the memory interface](Airbender/Review/Blake2G/Memory.lean)
and `Memory.soundness` derive mixing-input bounds from actual Sail initialization,
native matching and accepted writes. Caller-clock alignment and modeled controller
rows remain explicit; this claim does not establish full compression or a caller request.

The extended-round [memory interface](Airbender/Review/Blake2Round/Memory.lean)
and `Memory.soundness` likewise derive all state/message and pointer bounds from
initialized native history. The complete row includes preparation, SIGMA, eight
Clean G calls, finalization, controller and addresses. An exclusive round mask
is still a caller condition; the local circuit only checks each control bit.
A caller request, full compression sequence and cross-family hash transport are
not established by these row claims.

Keccak's [public claims](Airbender/Review/Keccak/Theorems.lean) cover every
lane mode against the original Clean reference: Iota/column parity, both D mixes,
Theta, Rho and both Chi calls. Native controls, gates, lookups and actual limb
transfers supply the operation results and word ranges. Rho uses Theta's writes;
the two-call D/Chi claims include their scratch/read transfers.
[Modeled setup rows](Airbender/Review/Keccak/Tables.lean) still have an unproved
Rust-generator binding. Physical column selection, the complete controller
schedule, ABI/caller binding and full permutation composition remain open.
The [initialized Keccak interface](Airbender/Review/Keccak/Memory.lean) derives
all read/write/terminal word bounds across all seven active modes. Active calls
remain explicit: inactive padding has no local write-preservation constraint.
The local transfer mappings still need actual Sail memory transport and schedule
binding; these claims do not establish a complete Keccak invocation.

The extended-control claims cover [x12](Airbender/Review/Blake2Round/Control.lean)
and [state/message preparation](Airbender/Review/Blake2Round/Preparation.lean) for
any XOR setup. Preparation uses Clean’s common IV with Airbender’s digest/block
parameter adjustments; its control flags and internal words are mapped to the
artifact. Input labels guard the word-column mappings. These claims do not need
round-mask exclusivity. [Message permutation](Airbender/Review/Blake2Round/Schedule.lean)
reuses G’s SIGMA schedule and requires an exclusive caller mask; the imported
selector equations are normalized before applying that condition. Its XOR queries
reuse G's modeled setup and checked XOR semantics;
Rust setup provenance remains unproved. Imported scaled ranges prove state/message
alignment, with explicit field compatibility. The four column G calls reuse the
native G fragment through checked carry/query renaming and table-column padding;
their outputs are ranged by queries. Four input-word bounds per call remain explicit.
Diagonal-call composition, final XOR and memory coverage remain open. The serialized
BLAKE2 inverse constants restrict this artifact to BabyBear; a 128-bit artifact needs
its own coefficients. The Rust caller
expects an exclusive round mask, which is not a local constraint; that domain
must be explicit when establishing the complete round behavior.

## Small review surface

Start with these shared definitions:

1. [Execution claim](Airbender/Review/Trace/Soundness.lean): accepted native
   traces realize original Sail execution and terminal PC/register/RAM values.
2. [Public conditions](Airbender/Review/Trace/PooledExecution.lean): initial
   state/program/domain, configuration, modeled tables and terminal-PC normalization.
3. [Native matching](Airbender/Review/Trace/Model.lean) and
   [family registry](Airbender/Review/Trace/Pooled.lean): imported Clean constraints,
   native state/port columns and logical state/memory matching.
4. [Actual decoding](Airbender/Review/Trace/PooledProgram.lean) and
   [execution meaning](Airbender/Review/Trace/Execution.lean): public Sail decoding,
   original clauses, normal retirement and the shared `Realizes` conclusion.

[ADD/SUB's model](Airbender/Review/AddSub/Model.lean) retains a visible per-circuit
assumption list. `circuitModel` checks its imported constraints and shared
matching/membership; `InterfaceAssumptions` supplies public initialization and modeled
tables. The [per-circuit theorem](Airbender/Review/AddSub/Theorems.lean) derives
decoder, operand/immediate/PC bounds and register reads using Trace helpers.
[RowPosition](Airbender/Review/Trace/RowContext.lean) maps earlier native writes to
the row's input state; it requires no reads or ISA execution. Write determinism
connects this mapping to the proved initialized history. Standalone calculation
interfaces/lemmas remain internal in `Proofs/AddSub/RowModel.lean` and `RowClaims.lean`.

[Word memory's model](Airbender/Review/WordMemory/Model.lean) uses the same shared
row position. Its visible assumptions are public initialization, modeled tables,
ordinary addresses and flat-memory configuration. The per-circuit theorem derives
effective-address bounds and actual LW/SW effects from initialized history and
original Sail decoding/execution. No read value or successful memory access is a
premise. Standalone transport/calculation interfaces remain under `Proofs/WordMemory/`.
[Mul/div's model](Airbender/Review/MulDiv/Model.lean) keeps only public initialization
and modeled tables. Shared history derives operands/reads and selector choices;
the common register projection checks native destination and PC effects.
[Shift/binop's model](Airbender/Review/ShiftBinop/Model.lean) needs only public
initialization. Its instruction mapping identifies the public instruction's original
Sail clause, with no claim about its result; shared history proves that execution.
[Subword memory](Airbender/Review/SubwordMemory/Model.lean) retains the same public
conditions as word memory. Shared history derives the aligned cell, reads, merged
store effects and original Sail execution; the ROM fixture uses the proved public-byte view.

The same initialized history connects all six admitted families, including native
ROM shadow slots and public bytes. Public conditions and logical
matching/membership remain explicit. Import/Sail generation and modeled-table
fidelity need separate review; cryptographic enforcement is deferred.

Local custom-operation and other-family claims retain their stated conditional
scope. [Verification status](VERIFICATION_STATUS.md) is the current coverage/gap
inventory, including inactive rows, discarded-load profiles, oracle coverage and
terminal-PC normalization. Supporting proofs are machine checked in `Proofs/`;
faithful importing remains a separate `Import/` audit obligation.

## Unchecked connections

- **JSON → Clean objects:** inspect [Parse.lean](Airbender/Import/Parse.lean),
  [Schema.lean](Airbender/Import/Schema.lean),
  [Coefficients.lean](Airbender/Import/Coefficients.lean),
  [Embed.lean](Airbender/Import/Embed.lean) and
  [the artifact declaration](Airbender/Review/AddSub/Artifact.lean).
  Range-query addresses are resolved through `placement_data`; missing or ambiguous
  logical variables are rejected. The kernel checks the emitted Clean object, not
  import fidelity or the correspondence with the compiled lookup argument.
- **Sail → generated Lean:** inspect [generation](scripts/generate_sail.py),
  [the slicing adapter](scripts/sail_slice.ml) and
  [provenance](generated/sail-rv32/provenance.json).
  The generator extracts the unique normal `F_Base` nextPC assignment verbatim from
  pinned `run_hart_active` into `extracted_base_pc.sail`, then compiles it with Sail.
  Review that extraction and the chosen decoded four-byte path: the complete fetch
  driver, interrupt handling and exceptional branches are not imported into this claim.
  Pins/hashes identify files; they do not certify extraction, compilation or pruning.

Compiled-gate correspondence, cached equivalence, lookup/memory arguments and
protocol soundness are separate milestones in [the plan](FORMAL_VERIFICATION_PLAN.md).
Use [the axiom audit](Airbender/Checks/Axioms.lean) to check the actual proof dependencies.

The [nondeterminism read contract](Airbender/Review/AddSub/NonDeterminism.lean)
receives an external stream and position independently of the witness. Its
`ReadMapping.responsePort` is an explicit input interpretation, not a circuit
constraint or proof that Airbender authenticates a fixed stream. The original
constraints permit different responses. Single-read register/PC effects, actual
CSR decoder binding and whole mixed-trace execution are checked. The trace
`StreamPorts` boundary connects the independent stream. Native clocks derive its
positions; the final reference counter equals the accepted trace’s read count.
The native boot claim preserves that connection through the physical ROM view.
The [primary pooled mixed claim](Airbender/Review/Trace/Soundness.lean) composes
all six admitted families with those reads/hints, using the same public boot
conditions and explicit stream-port boundary. Bounds and native reads are derived
through the shared history; terminal PC/cell values and exact consumption are conclusions.
Hints consume no stream word and claim no application I/O behavior.
