# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
A proof does not establish that its definitions express the intended claim or
that an imported object faithfully represents the source artifact.

## Origin and status

| Component | Origin | What needs checking |
| --- | --- | --- |
| Lean kernel and standard axioms | Reused foundation | Accepted proof-checking foundation |
| Mathlib and Clean | Pinned upstream dependencies in `.lake/packages` | Definitions must fit their use; their proof terms are checked by Lean |
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

## Small review surface

All first-read definitions and claims are under `Airbender/Review/`:

1. [Shared properties and circuit relation](Airbender/Review/Properties.lean):
   arbitrary witnesses, declared observables, and explicit interface conditions.
   [Word encoding](Airbender/Review/Word.lean) and [field selection](Airbender/Review/Field.lean)
   define the representations used by these claims.
2. [Circuit model](Airbender/Review/AddSub/Model.lean): imported constraints,
   variable mapping and external decoder/range/register obligations.
3. [Sail interface](Airbender/Review/Sail.lean): original instruction inputs,
   fixed initial state, successful retirement and native destination/PC effects.
4. [Public theorems](Airbender/Review/AddSub/Theorems.lean): conditional soundness
   for generic prime fields and BabyBear, against the Sail specification.
   [Custom modular definitions](Airbender/Review/AddSub/Modular.lean) give the four
   project-specific word operations, native register/PC effects and interface assumptions.

Supporting proofs are in `Airbender/Proofs/`; their correctness is machine checked.
Import code remains a separate audit obligation in `Airbender/Import/`.
The assumptions do not assert the arithmetic result or carry bits. Current
coverage is ADD/ADDI/SUB/LUI/AUIPC destination and PC effects on the normal decoded
four-byte path, including x0/NOP preprocessing. The destination index is mapped to the JSON's
decoder variable. Discarded writes require successful original Sail reads, without
equating those values to the preprocessed zeros; operand bounds are unnecessary there.
Result and final-PC bounds follow from imported static range queries;
operand/immediate and initial-PC bounds remain external. AUIPC uses Sail's actual
PC read and U-type immediate construction under explicit mapping contracts.
The serialized PC inverse
is checked for BabyBear and explicit in the generic theorem. The normal-path
initialization and `tick_pc` connection are proved over generated/native semantics;
fetch/interrupt/exception handling, completeness and contract discharge remain pending.
The timestamp theorem similarly checks the serialized inverse and proves field
carry equations. Timestamp range queries are not emitted yet; no integer ordering
claim follows. Execute = 0 does not itself establish architectural stuttering:
the imported local relation admits advancing PC and nonzero destination limbs.
Custom modular soundness covers canonical BabyBear values and native register/PC
effects, including Montgomery multiplication, FMAMOD's old-destination read,
aliasing and x0 preprocessing. Standard and custom claims share the native step
relation and retirement proof. The small handwritten custom arithmetic definition
must be checked against the pinned project document; it is not an upstream Sail clause. Local delegation zero values
and read timestamps are checked; dispatch identity and memory effects remain
interface obligations. Nondeterminism-write soundness checks the project-specified architectural no-op
and PC retirement; source-hint/application-I/O behavior is outside the claim.
Nondeterminism-read agreement with a fixed response needs an external binding.
Conditional composition applies to standard and custom rows, requires an explicit
match of native states and does not discharge the execution/memory argument.

Jump/branch/SLT uses the same import and Clean semantics. Its
[public claims](Airbender/Review/JumpBranchSlt/Theorems.lean) cover local arithmetic
and native Sail SLT/SLTI/SLTU/SLTIU register/PC effects through one model and
shared soundness theorem. All four fixed comparison/cleanup queries
are now emitted; timestamp queries are still excluded. The table rows in
[Lookups.lean](Airbender/Review/Lookups.lean) reconstruct the
Rust generators symbolically and share the unproved table-provenance gap.
A checked counterexample shows that the local relation does not enforce a 16-bit
final-PC high limb; comparison soundness explicitly assumes that state/ROM bound and
four-byte input alignment. Its initial high-PC bound follows from a lookup, and
PC wraparound is supported. Decoder identity and agreement with successful native
Sail operand/PC reads remain interface obligations. Immediate preprocessing calls
native Sail sign extension. Pure RTYPE/ITYPE and M writes to x0 use the separate
[ADD/SUB discarded-write contract](Airbender/Review/AddSub/Discarded.lean), matching
`Instruction::pure_from_imm` NOP preprocessing: the comparison-family decoder
rejects rd = 0. The original native Sail reads must succeed; their values need
not match the preprocessed zeros. This path uses the existing ADD/SUB PC proof
and therefore excludes 32-bit PC overflow. Decoder routing remains an external
obligation. Local branch resolution and PC selection/alignment are checked, with
explicit operand/offset and final high-PC bounds. Local JAL/JALR link and target
proofs include wrapping, x0 masking and odd-target bit-0 cleanup. Selector identity,
input bounds, JAL offset parity and the final high-PC bound remain interfaces;
the imported bit-1 check derives four-byte target alignment. The regenerated
control-flow clauses now compile with the explicit emulator-default platform
binding. All six standard branches share native Sail state/PC soundness through
[one contract](Airbender/Review/JumpBranchSlt/Branch.lean). The target/outcome and
alignment are proved, while operand/offset bounds, decoder identity, successful
native register reads and the final-PC high bound remain interfaces. Sail reads
`misa` even for aligned targets: its value is unrestricted, but it must be initialized.
JAL/JALR share [native-state soundness](Airbender/Review/JumpBranchSlt/Jump.lean),
including wrapping, x0 and aliases. The slice retains the original Zicsr module's
configuration clause needed by JALR. Its landing-pad update is proved inactive
under explicit native Machine-mode and MLPE-clear CSR reads; enabled landing pads
and other privilege modes are outside this claim. Target/link values are derived,
while input bounds, decoder identity and initialized native reads remain interfaces.

Unsigned mul/div imports 43 equations (including directed definitions), eight
range16 queries and eight fixed-table queries. Scratch aliases are accepted only
when the JSON's forward and reverse maps agree and resolve to a unique placement.
The shared low-byte and 13-bit range tables reconstruct Rust generators; table
provenance remains unproved. MUL/MULHU and DIVU/REMU for all divisors share native register/PC
soundness against the original generated Sail M-extension clauses. Decoder
selection, successful register/PC reads and left-operand/initial-PC bounds are interfaces;
the zero flag, result and final-PC bounds are derived. The PC proof requires the
serialized inverse and excludes 32-bit overflow. The byte-column proof now
establishes an exact integer product-plus-remainder relation, with `p ≥ 2^29`,
decoded selector identity and left-operand limb bounds explicit. A strict remainder
bound is proved from the imported comparison and range queries, then native
division uses Lean's quotient/remainder uniqueness theorem. The single
[mul/div contract](Airbender/Review/MulDiv/Model.lean) covers all four selectors and zero/nonzero
divisors. MUL uses the original signed low-product clause, MULHU the unsigned
high-product clause. M-extension x0 preprocessing reuses ADD/SUB’s discarded-write contract; original
reads must succeed, without arithmetic bounds or agreement with the NOP operands.
The decoder-to-NOP binding remains an explicit interface.
The regenerated snapshot adds
the upstream MUL/DIV/REM clauses without altering the existing ISA clauses.

Shift/binop imports 52 retained equations, two final-PC range queries and five
dynamic-tag byte queries. The importer preserves tags and checks query sets,
padding, scratch placement and the setup/decoder boundary. Local flags and the
PC increment are proved with initial bounds and the serialized inverse;
final bounds follow from lookups. Its [fixed byte tables](Airbender/Review/ByteTables.lean)
are handwritten Rust reconstructions using Clean static membership and byte
utilities. Their setup correspondence is unproved; decoder contracts and cryptographic
memory/lookup arguments remain separate obligations. XOR/OR/AND, SLL/SRL/SRA
(including immediate forms) and REV8 share one [Sail contract](Airbender/Review/ShiftBinop/Model.lean)
and native register/PC soundness claim. Selected tagged membership forces each
operand/result byte, and the imported assembly equations reconstruct the word;
operand and destination ranges are derived. The mapping binds preprocessed byte
queries to independently fixed native operands. Immediate binary words use Sail
sign extension; shift counts follow from truncation and decoder mapping. REV8's
original Zbb byte loop is retained and proved to match tag-5 contributions with
zero count. Selector identity, immediate-shift legality and successful native reads
remain interfaces. The field bound is `262144 < p`, with explicit serialized PC
inverse; no desired result or scratch bounds are assumed. REV8 and immediate x0
shifts reuse the ADD/SUB NOP/native-retirement claim.

Word memory's ROM query is imported as a native Clean lookup with a caller-supplied
nine-column table. Program/setup correspondence remains an interface; no table
extraction is claimed. Logical placement resolves its three ranges to the ROM
separator residue and final-PC limbs. Local address arithmetic requires bounded
source/immediate/address words. ROM classification and store exclusion follow from
that residue; copied intermediates are eliminated in the data query. RAM transfer
requires a table-wide zero-tag law, while active ROM loads give native membership
at the selected address. Neither assumes the desired instruction result. The
program table is still external. RAM LW/SW now share a native Sail soundness
claim for address, data, register and PC effects; ROM loads extend the same theorem
under a uniform program-image binding. It quantifies over field-valued table data,
decoded canonically, avoiding ambiguous natural-number representations.
Both cases reuse the register-family
retirement proof with a native memory-write projection. Byte order and writes
come from the pinned sequential interpreter. The memory contract uniformly relates
`vmem_read`/`vmem_write` to native byte-memory effects for arbitrary data and nextPC;
it does not assume a circuit output or successful whole-instruction execution.
Discharging it requires the platform's translation, alignment, privilege and access
guarantees. Read-port values must agree with the independently fixed pre-state.
The table/image binding is an explicit interface, distinct from deferred extraction.
Stores' exclusion from ROM is proved; RAM-address scope is no longer assumed.
The shared two-row composition lemma also accepts memory-write projections;
state links still require external execution/memory interfaces.

Subword memory preserves all five ranges and two data-query sets against a
caller-supplied tagged Clean table. The importer checks widths, padding, table
regions and query identities; metadata guards bind the proof columns. Local
alignment and offset uniqueness use the imported low-address and cell-index
ranges. Only the selected high-address and input-word bounds remain external to
that arithmetic lemma. RAM/ROM load keys and store keep/preserve expressions are
proved from the equations. The [modeled setup](Airbender/Review/SubwordTables.lean)
reconstructs Rust's seven tagged regions, with an independent padded program-word
function. RAM-load membership forces bounded limbs and agrees with Sail's actual
byte/halfword extension; both imported RAM modes derive result bounds from it.
Extraction/Rust binding remain gaps; ROM membership is decoded below.
The fixed store-table semantics now prove byte clearing/placement, exact SB/SH
merged limbs, unchanged opposite halves and output bounds. The proved byte-window
encoding connects the merged cell write to the original native narrow write, with
identical complete states. The shared soundness theorem includes RAM SB/SH and
retirement; the old-cell read is independently fixed by the operand-computed address.
LB/LBU/LH/LHU RAM soundness now connects the packed query to the independently
fixed read-port word, derives native byte/halfword reads from the original four-byte
read, and reuses Sail LOAD and retirement for full register/PC effects. The read-port
contract names the aligned address computed from source operands, not a witness
output. Input bounds, the selected high-address bound, decoder modes, successful
native reads and uniform platform transport remain explicit. ROM loads now use
the same native execution/retirement claim: membership proves the packed address,
sign/position bits and exact program slice. A uniform aligned-cell program-image
binding supplies the native read; it does not mention a circuit result. That image
binding remains an interface obligation. The shared claim requires `p > 2^25` so
ROM packing cannot wrap in the field. A concrete LBU fixture establishes satisfiability without
assuming witness-generation correctness. All load widths reuse one native Sail
execution lemma; LW remains checked through it.

Runtime-error compatibility is proved over Sail's existing effects. Terminal output
and reservation externals are now supplied through an abstract `MemoryPlatform`
parameter: no implementation or behavioral axiom is added. The generator inserts
only a typeclass/header with lifted aliases; the manifest records the exact insertion
and the original emitter hash. Instruction bodies remain upstream output.

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
