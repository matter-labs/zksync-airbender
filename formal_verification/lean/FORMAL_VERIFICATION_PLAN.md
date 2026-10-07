# Circuit formal verification plan

Current coverage and gaps are in [Verification status](VERIFICATION_STATUS.md).
Update that snapshot after each completed task; do not append a change log there.

## Objective and first deliverable

Prove ADD/ADDI/SUB soundness against reused Sail RV32 semantics for arbitrary
assignments satisfying the richer constraints imported from the generated no-cache
JSON. Keep decoder, range and register/memory interfaces explicit. The witness
generator is not an assumption of soundness.

The first deliverable covers the full declared instruction step. The current
prototype proves combined destination/PC effects, including `x0`, for the normal
decoded four-byte Sail path. Fetch, interrupts and exceptions remain outside that claim. Compiled gates and protocol
soundness are later claims.

## Design decisions

- Import the generated JSON directly into native **Clean** expressions and flat
  assertions and lookups. Clean is the sole expression/constraint model for circuit proofs.
- Reuse the actual **Sail** standard-instruction semantics. Keep arithmetic
  calculations inside proofs; custom operations need an explicit project spec.
- Keep shared definitions of soundness and completeness. Conditional
  statements apply those definitions directly. Separate
  constraint satisfaction, observable mapping and external assumptions.
- Reuse Mathlib/Lean/Clean lemmas before introducing equivalent infrastructure.
  Circuit families should establish artifact-specific premises and reuse shared proofs.
- For lookups, reuse Clean's `StaticTable` and native lookup semantics. For later
  memory/state proofs, start with `Clean.Utils.SourceSinkPath` (balanced transitions
  imply a path), `Clean.Utils.OfflineMemory` (offline/online memory consistency),
  and `Clean.Table.Inductive` for ordered row composition where its interface fits.
  Prove the Airbender-specific encoding, timestamp, initialization and argument
  premises; retain Sail as the instruction reference.
- Parameterize shared proof lemmas over the field. Our circuit interface uses
  prime fields `ZMod p` for canonical word decoding; the current destination-word
  theorem requires `p > 196608`. New claims must account for field-dependent
  serialized constants. Keep artifact compatibility premises separate from reusable
  algebra; actual large-field artifact import remains pending.
- Start from `_layout_no_caches_gkr`. Cached helper equivalence follows later.
  SSA witness-generation artifacts and schedules are outside this proof target.
- Keep original upstream source, generated reference files and our code separate.
  Put definitions, assumptions and public claims in `Airbender/Review/`, supporting
  proofs in `Airbender/Proofs/`, and the unchecked JSON pipeline in `Airbender/Import/`.
  Minimize the code and documentation a reviewer must read. Keep one public
  reference interface, with encoding and execution lemmas in the proof area.
  Public theorem files contain soundness claims, not copies of numeric helper
  lemmas. Jump/branch/comparison contracts use metadata-checked column names;
  decoder, bound and native-state interfaces remain visible and separate.

## Current proof path and assumptions

```text
no-cache JSON → Clean assertions + static lookups → arithmetic lemmas → Sail execution
```

All 30 retained equations and six 16-bit range queries are emitted as transparent
Clean operations, parameterized by the prime modulus. Queries are mapped from
physical addresses to logical variables through `placement_data`. Clean's native
satisfaction theorem supplies both assertion equations and lookup membership.
No duplicate local interpreter or translation bridge remains.

**Table provenance gap:** the queries are imported, but the fixed 16-bit table
is reconstructed by hand from Airbender's Rust setup generator. Its rows are not
extracted, and the Rust-to-Lean table binding is unproved.

The standard-branch theorem assumes:

- active row and decoded selector/preprocessing values;
- bounded initial-PC limbs for every row; bounded operand/immediate limbs for
  nonzero destinations (decoder/memory obligations);
- input-word encoding and canonical output decoding through named variables;
- successful actual Sail reads, matching circuit words for nonzero destinations,
  and Sail immediate preprocessing for ADDI/LUI/AUIPC.

The result equation, carry bits and result-limb bounds are derived from the imported
relation. The six range queries cover result, final-PC and modular-comparison limbs;
they do not bound input operands. Soundness targets Sail directly. The initial
Sail state is fixed input. [The README](README.md) links the compact review entry points;
[the trust map](TRUST_AND_REVIEW.md) identifies unchecked connections.

## Implementation sequence

1. **Pin reused foundations.** Done for Lean/Mathlib, Clean and Sail. Clean's selected
   modules build unchanged under the existing toolchain. Its broader DSL/gadget/
   composition interfaces remain candidates for later obligations.
   `SourceSinkPath` also builds unchanged. Importing `OfflineMemory` currently fails
   on two instance declarations in `Clean.Circuit.Explicit` under Lean 4.31;
   resolve that compatibility issue before integrating its memory theorems.
2. **Define shared properties and interfaces.** Done: constraints, representation
   and assumptions are separate; conditional claims reuse the shared definitions
   directly. The model lists its contracts together; one short theorem file collects
   the public claims. Completeness is defined but not yet proved.
3. **Import the real artifact.** Done for BabyBear: strict schema decoding,
   Montgomery coefficient conversion, native Clean emission, embedded source bytes
   and variable-role guards. Import/emission fidelity remains a review obligation.
4. **Prove arithmetic and Sail destination-word behavior.** Done for ADD/ADDI/SUB,
   including the concrete BabyBear field instance.
5. **Import range checks and derive result bounds.** Done: all six 16-bit queries
   use native `StaticTable` membership, replacing the result-bound
   assumption for the modeled table. Generated-table extraction remains pending.
   Input bounds still require decoder/memory contracts. The lookup
   argument itself and its compiled encoding are separate proof obligations.
6. **Finish the declared standard-instruction step.** Connect PC sequencing,
   architectural register projection and preprocessing of writes to `x0`.
7. **Review the complete claim.** Check interface assumptions, exact instruction
   and field coverage, artifact identity, and axiom dependencies.

## Next work: expand circuit coverage

**Approved; implementation started.** The next pass completes the ADD/SUB
family's instruction behavior, then applies the same work to other circuit families.
Lookup-table extraction, richer/compiled equivalence,
cached equivalence and cryptographic lookup/memory soundness are deferred.
Keep the existing table-provenance gap explicit while extending the proofs.

**Progress:** phase A's local PC equations and final-limb bounds are kernel-checked.
They imply `finalPC = initialPC + 4` with no 32-bit overflow, independently of row
selectors, under bounded initial limbs. The imported inverse identity is checked
for BabyBear and explicit in the generic lemma. The main soundness theorem now composes those equations with actual generated
Sail initialization, execution and retirement effects. LUI/AUIPC
destination soundness now reuses the generated upstream UTYPE clause, including
AUIPC's actual PC read. The slice also retains upstream PC accessors and `tick_pc`;
the generator also extracts the default next-PC assignment verbatim from the
normal `F_Base` driver branch. Its source hash/line and extracted statement are
recorded; extraction and path selection remain unchecked. Fetch, interrupts and
exceptions are excluded from the decoded-path theorem.
The shared soundness claim also covers writes to x0 and NOP preprocessing, retaining
the original Sail instruction and deriving discarded GPR writes plus PC advance. Original
reads must succeed; operand bounds and value agreement are required only for nonzero
destinations. The destination index is now explicitly bound to its imported variable.
Local Booleanity of the execute flag and all nine selectors is proved from the
imported equations. Selector identity/exclusivity remain decoder guarantees;
the standard-row contract now excludes both delegation and nondeterministic selectors.
Timestamp assertions now yield the four-tick, 19-bit-limb carry equations, using the
same field lemma as PC. Timestamp range queries are parsed but not emitted, so
integer timestamp bounds and global ordering remain outside this claim. A checked
inactive-row witness advances PC and permits a nonzero destination; execute = 0
alone does not establish an architectural stuttering step.
The project specification is now pinned locally; custom-branch work can proceed
from its BabyBear/Montgomery and nondeterminism definitions.
All four modular branches now have architectural soundness claims against that
custom spec, with canonical BabyBear output derived from comparison equations and
lookups. MULMOD/FMAMOD use the serialized Montgomery inverse, checked against
radix 2^32. Native Sail reads bind both operands and FMAMOD's old destination before
the write, including source/destination aliasing. Writes to x0 are discarded after
original reads; the circuit uses zero-operand ADD preprocessing. PC advancement
uses the same native retirement proof as standard instructions. The shared
soundness property and native state relation are reused; no extra machine or
constraint model is added. These custom operations are not upstream Sail ISA clauses.

**Verified PC milestone:** the single standard circuit model now returns destination
and final PC, mapped to the imported variables. Sail's native `nextPC` and `PC`
updates are composed with destination effects; GPR writes preserve `nextPC` and
preparation preserves operand reads. Tests cover a 16-bit PC carry, source/destination
aliasing and x0 retirement. The generic combined theorem explicitly requires the
serialized PC inverse; BabyBear discharges it. Full build, importer checks and axiom
audit verify the milestone. Conditional two-row composition is also checked: both executions agree when the
second fixed input state equals the first projected result. The proof does not
establish that execution/memory arguments enforce this link. Delegation selection
now forces zero source limbs, zero read timestamps and zero destination limbs;
dispatch identity and delegated memory effects remain external.
Nondeterminism-read/delegation architectural contracts and phase F remain open.
The modular milestone passes the full build, 17 importer checks and axiom audit;
concrete tests cover reduction, FMA aliasing and x0 for all four operations.

**Nondeterminism-write milestone:** the project's CSRRW x0, 0x7C0, rs1 no-op
now has a native-state/PC soundness claim. Decoder preprocessing remains explicit;
no source-hint or application-I/O correctness is claimed. It reuses the imported
PC equations and the shared native retirement rule. Conditional composition now
applies to both standard and custom executions through one shared lemma.

**Custom interface limitation:** the retained arithmetic constraints intentionally
leave nondeterminism-read destination values free except for range checks
(`add_sub_family/circuit.rs`). They cannot establish agreement with an independently
fixed oracle response. Such a claim requires an external response binding; do not
supply that binding by defining the oracle from the output witness. Delegation
identity is carried by decoder/preprocessed CSR and permutation interfaces, not by
the six zero assertions alone. These interface obligations are distinct from the
deferred cryptographic arguments.

### A. PC update and a shared transition interface

1. **Inventory the actual PC relation.** Identify the imported PC assertions,
   initial/final variable roles, range queries and execution-flag behavior. Establish
   what is enforced even on inactive rows. Add role guards for variables used by proofs.
2. **Check field compatibility before generalizing.** The BabyBear JSON's PC
   assertions use the serialized inverse of 65536, whose signed representative is
   `-30720`. It is an inverse in BabyBear, not an inverse under arbitrary prime moduli.
   Prove the required identity for this artifact. Keep arithmetic lemmas generic
   with explicit inverse premises; preserve the existing generic destination theorem.
   Do not reinterpret or replace a serialized constant to make a theorem hold.
3. **Prove the PC equations from Clean satisfaction.** Recover the low-limb carry
   expression and its Boolean property, then the high-limb equation. Derive final-PC
   limb bounds from the existing imported lookups. Reuse field-to-natural and word
   lemmas; do not assume the desired PC increment.
4. **Resolve PC boundaries.** Prove the actual successor behavior, including a
   carry across the 16-bit boundary. Analyze the top of the 32-bit address space:
   the artifact has no explicit second wrap carry. Record whether satisfying rows
   exclude overflow rather than assuming wrapping or adding an artificial range
   precondition. Check the project's supported four-byte instruction profile.
5. **Bring in the actual Sail PC semantics.** The generated slice retains
   RTYPE/ITYPE/UTYPE execution, PC accessors and `tick_pc`, but omits default next-PC
   initialization. Find the smallest relevant
   upstream PC-update/retirement code, extend the existing generation slice as needed,
   and preserve its pins/provenance. Do not write a replacement PC specification.
6. **Extend the observable transition once.** Add initial/final PC to the shared
   instruction interface and map them to the imported variables and Sail state.
   Keep one Sail reference surface and the existing shared soundness definition.
   Separate PC input interpretation from enforced PC equations and external contracts.
7. **Compose destination and PC soundness.** Strengthen ADD/ADDI/SUB claims to cover
   destination effects and the proved PC transition against the reused Sail semantics.
   State exactly which fetch, decoding, memory and architectural-step obligations remain.

**Acceptance:** kernel-checked PC and combined soundness claims; explicit artifact
field coverage and overflow behavior; no new handwritten standard-instruction spec.

### B. Finish the standard branches in this family

8. **Add LUI.** Trace its decoder preprocessing into the existing addition selector.
   Extend the generated Sail slice to the upstream UTYPE clause. Prove the shifted
   immediate and zero-source mapping, reusing the existing addition calculation.
9. **Add AUIPC.** Select the imported PC-plus-immediate equations and connect them
   to Sail's original PC read and UTYPE execution. Reuse the PC input mapping,
   carry/word arithmetic and PC successor proof. Include word-boundary behavior.
10. **Cover NOP and writes to x0.** Airbender preprocesses discarded writes into
    addition with zero operands. Connect original instruction inputs to that
    preprocessing and Sail's zero-register behavior. State architectural effects
    rather than requiring a unique discarded ALU result. Keep these cases within
    the same reference interface and shared soundness property.
11. **Prove the register effects precisely.** Account for unchanged registers and
    operand/destination aliasing, including equal source registers and writes back
    to a source register. Reuse Sail's register semantics and existing write lemmas.
    Avoid another register-state wrapper or a parallel local machine model.

**Acceptance:** standard branch coverage for ADD, ADDI, SUB, LUI, AUIPC and the
relevant NOP/x0 preprocessing cases, with destination effects and PC behavior.

### C. Close local row obligations

12. **Review selector assumptions.** Derive Boolean and exclusion properties that
    the imported constraints actually enforce. Retain instruction selection and
    decoder guarantees as explicit contracts wherever the equations do not imply them.
    Include all nine decoder flags in the coverage inventory.
13. **Handle inactive rows.** Define the claim's scope when the execute flag is zero.
    Distinguish locally constrained dummy values from architectural effects; do not
    assume an inactive row stutters merely because the flag is zero. Prove the local
    masking facts needed by the exposed relation and list remaining argument contracts.
14. **Check cycle/timestamp behavior.** Inspect the machine-state layout and imported
    equations for locally enforced updates. Prove available facts with explicit bounds;
    if ordering or advancement comes only from another argument, record that dependency.
    This does not include proving the memory argument.
15. **Reduce interface assumptions.** Audit every premise used by the expanded
    proofs. Derive bounds from imported queries or native word decoding wherever
    justified; retain operand/immediate range guarantees not supplied by this circuit.
    Remove unused assumptions without weakening the stated architectural claim.

**Acceptance:** the model shows exactly what the local constraints prove and what
its decoder/memory/environment interfaces still promise.

### D. Cover the custom branches

16. **Pin and review the custom-operation specification.** Locate the authoritative
    project semantics for modular operations, delegation and nondeterministic I/O.
    Fix the target modulus, input/reduction policy and externally supplied values.
    Keep custom specifications small and separate from standard Sail behavior.
    If a specification is missing or ambiguous, record the blocker and continue
    independent work; do not substitute the witness generator as the specification.
17. **Prove canonical modular outputs.** Use the imported comparison equations and
    intermediate range queries to establish the required output range. Develop
    reusable reduction and carry lemmas, with artifact-specific field premises.
18. **Prove modular addition and subtraction.** Instantiate those lemmas for the
    two selectors and prove the reviewed custom relations. Cover reduction boundaries
    and state the valid input domain explicitly.
19. **Prove modular multiplication.** Derive its equation from the imported assertion
    and combine it with the canonical-output proof. Reuse the target-modulus machinery
    rather than duplicating a second arithmetic model.
20. **Prove modular fused multiply-add.** Expose the old destination/register input
    needed by this branch, relate it to the register interface, and reuse multiplication,
    reduction and canonical-output lemmas. Include destination/source aliasing cases.
21. **Cover nondeterministic read and write.** Expose oracle inputs and observable
    I/O events in the reviewed custom contract. Prove the local register/PC/effect
    relation; an external input must not be defined from the output witness to make
    soundness tautological. Do not reintroduce determinism as a circuit property.
22. **Cover delegation dispatch.** Prove the local dispatch identity and relevant
    register/PC effects against a reviewed request/response contract. Keep correctness
    of the delegated computation and its argument as explicit downstream obligations.

**Acceptance:** each remaining branch has a precise soundness claim or a documented
specification/interface blocker. Custom claims are not labeled as upstream Sail proofs.

### E. Consolidate and check the expanded model

23. **Compose family coverage.** Present one shared soundness statement whose cases
    cover the declared instructions and effects. Centralize selectors, variable roles,
    field premises and reused proof lemmas; keep routine calculation details in `Proofs/`.
24. **Check conditional row composition.** Reuse relation/list or suitable Clean
    composition lemmas to connect rows when their observable states are given to match.
    State that chaining premise explicitly. Proving that the execution argument
    establishes it remains deferred with memory/argument soundness.
25. **Review and machine-check.** Run scoped Lean checks during implementation and
    the full build/importer checks/axiom audit at integration points. Exercise concrete
    carry, borrow, PC-boundary, aliasing, x0, inactive-row and custom reduction cases
    where they expose a remaining risk. Confirm no `sorry`, new project axioms or
    unsupported full-step/large-field claims. Stop redundant testing once verified.
26. **Simplify the review surface.** Remove obsolete contracts, helper wrappers and
    duplicated statements. Keep the review path to shared properties, imported artifact,
    input/output mapping, external assumptions and public claims. Update the scope and
    trust notes concisely; document counterexamples and unresolved gaps explicitly.

### F. Expand to other circuit families

27. **Inventory and order the remaining families.** Match each no-cache layout to
    its standard instructions or custom operations. List branches, observables and
    external interfaces, and prioritize families that reuse the established machinery.
28. **Transfer the foundations to a second family.** Import its richer constraints
    directly into Clean and reuse the shared soundness property, Sail interface and
    arithmetic lemmas. Generalize helpers only where needed; do not copy the ADD/SUB
    model or introduce a second constraint interpreter.
29. **Repeat the coverage work for each family.** Prove its branches, PC behavior,
    register/effect semantics and local row obligations against Sail or the reviewed
    custom specification, as in phases A–D. Reuse established proofs wherever the
    equations or interfaces agree, including x0, aliasing and inactive-row handling.
30. **Audit assumptions and field coverage per artifact.** Derive guarantees supplied
    by imported constraints and lookups; expose the remaining decoder, memory and
    environment contracts. Check serialized coefficients before applying generic field
    lemmas. Keep deferred table provenance and argument proofs explicit.
31. **Integrate and review each family.** Apply phase E's machine checks and axiom
    audit, then expose a compact soundness claim through the same review structure.
    Maintain one coverage summary showing proved branches, effects, supported fields
    and remaining gaps; keep shared definitions and proofs in common modules.

**Acceptance:** the same verification contract and review path apply across circuit
families, with kernel-checked claims and explicit coverage rather than duplicated foundations.

### Family inventory and order

Counts below refer only to retained equations and imported 16-bit queries in the
standard no-cache artifacts. Other generic lookup relations need explicit semantics
and interface contracts; importing range queries alone does not cover those relations.

| Next family | Equations / range16 queries | First reusable slice or dependency |
| --- | --- | --- |
| Jump/branch/SLT | 26 / 4 | Two-limb addition/borrow, native Sail reads/writes/PC; comparison and alignment lookups |
| Unsigned mul/div | 43 / 8 | Carry/reduction algebra; multiplication and division edge cases |
| Shift/binop | 52 / 2 | Bitwise/shift lookup semantics; native RTYPE/ITYPE clauses already retained |
| Word memory | 27 / 3 | Effective-address arithmetic and explicit memory interface |
| Subword memory | 43 / 5 | Word-memory interface plus extraction/sign extension |
| Unified reduced machine | 129 / 13 | Reuse family proofs; alternative combined artifact |
| Bigint delegation | 136 / 34 | Reviewed custom operations and request/response/memory interfaces |
| BLAKE2 G function | 32 / 2 | Joint active-row controller, scheduled-message reads, full G state update and six addresses checked under read/write/frame interfaces. Selector bounds are shared; the mixing proof now uses only twenty imported arithmetic assertions and eighteen XOR queries. Next: instantiate that fragment for extended control; memory transport, bounds and setup provenance remain explicit |
| BLAKE2 with control | 352 / 2 | x12 high-limb range/next mask, all 208 XOR relations under the shared modeled setup, state/message alignment, all-mode state/message preparation, and SIGMA selection under an exclusive caller mask checked. Initialization reuses Clean’s IV; XOR semantics and scaled-range lemmas reuse G. Four column G calls now use the native G fragment and share its soundness/output-bound proofs. Next: connect the diagonal calls, compose all eight, then final XOR and memory/address interfaces; caller round-mask domain and setup binding remain explicit |
| Keccak special5 | 187 / 1 | Reviewed lane operations, bitwise lookups and control |
| Initialization/teardown | 0 / 0 | No retained assertions or ranges in this artifact: richer-level proof input is missing |

**Second-family progress:** jump/branch/SLT imports 26 retained assertions, four
range16 queries and all four fixed-table queries directly into Clean. Local flags,
timestamp carries and signed/unsigned comparison results are checked.
The resolution proof accounts for the packed key and requires `p ≥ 4194304`;
operand bounds and instruction identity remain explicit. Table IDs, zero padding
and placement are validated. Fixed table rows are symbolic reconstructions from
Rust, with the same unproved provenance gap as range16; extraction stays deferred.
SLT, SLTI, SLTU and SLTIU now share one model and soundness theorem, reusing
native Sail clauses and retirement for register/PC effects, aliases and 32-bit PC
wraparound. Immediate words are bound to actual Sail sign extension. Packed-key
decoding, subtraction borrow and destination projection are shared; signed
resolution is proved against native bitvector signed ordering.
Its model canonically decodes PC limbs, derives the initial high-PC bound from a
lookup and explicitly requires the final high-PC bound and four-byte alignment.
Operand bounds, decoder identity and native reads remain interface obligations.
Pure RTYPE/ITYPE writes to x0 now reuse one ADD/SUB discarded-write soundness
claim. This follows `Instruction::pure_from_imm` NOP preprocessing; the comparison
decoder rejects rd = 0. The original Sail clauses execute with successful original
reads, independent of the circuit's zero operands. The imported ADD/SUB PC equations
give native state preservation and PC advance without 32-bit overflow. The proof
covers comparisons, bitwise operations and register shifts together; decoder
routing remains explicit. Concrete tests cover every retained RTYPE/ITYPE tag with
nonzero original operands, immediate -1 and a PC limb carry. Branches and jumps
remain architectural targets. This discarded-write milestone passes the full build (3447 jobs),
23 importer checks, warnings-as-errors for the changed Lean modules and the
50-claim axiom audit with only the same three standard axioms. Concrete imported
rows cover both signed sign-change directions, the -1 immediate, destination/source
aliases, the unsigned borrow boundary, PC wraparound and the interface gap below.
The comparison milestone passes the full build (3441 jobs), 23 importer checks
and warnings-as-errors checks for all changed Lean modules. The axiom audit adds
no dependencies beyond `propext`, `Classical.choice` and `Quot.sound`.

**Local branch progress:** all six branch conditions now follow from the imported
subtraction and resolution lookup, sharing the comparison carry/key proofs.
Local PC selection is proved for taken/not-taken branches, including negative
offsets and 32-bit wraparound. Given even offsets and aligned initial PC, the
imported bit-1 check enforces four-byte alignment for taken targets. Operand/offset
bounds and the final high-PC bound remain interfaces. This local milestone did
not yet connect Sail stepping; native progress is below. Fourteen concrete satisfying rows cover all six tags,
equality, both outcomes and PC boundaries; a taken PC-2 row is rejected. The full
build (3451 jobs), 23 importer checks, changed-module warnings-as-errors and
55-claim axiom audit pass with the same standard axioms.

**Local jump progress:** JAL/JALR now share proofs for PC+4 links (including
32-bit wraparound and x0 masking) and target addition. The native bit-mask result
for JALR clears exactly bit 0; imported lookup membership and the bit-1 assertion
derive four-byte target alignment. Eight satisfying rows cover both selectors,
wrapping, x0/nonzero rd and odd JALR sums; a PC-2 target is rejected. Source/offset
bounds, direct offset parity and the final high-PC bound remain interfaces; the
initial high-PC and saved-link bounds follow from lookups. Full build (3455 jobs),
23 importer checks, changed-module warnings-as-errors and the 59-claim axiom audit
pass with only `propext`, `Classical.choice` and `Quot.sound`. Native Sail jump
execution now compiles; native-state soundness is checked below.

**Unsigned mul/div progress:** all 43 retained equations and 16 range/fixed-table
queries import into native Clean. Scratch lookups require agreement between both
emitted alias maps and unique placement. Shared fixed-table semantics now live in
`Review/Lookups.lean`; low-byte and 13-bit range membership reuse Clean primitives.
Flags, divisor/quotient/output bounds, low bytes, carry bounds and the divisor-zero
predicate are proved. DIVU/REMU with a zero divisor now have native register/PC
soundness against the original Sail M clauses, regenerated with unchanged pins.
Decoder selection, initial-PC bounds and successful native reads remain interfaces;
the desired output is not an assumption. Concrete imported rows exercise both
branches, destination/source aliasing and a 16-bit PC carry. PC overflow at 32 bits
is excluded by the relation. The full build (3467 jobs), 29 importer checks and
70-claim axiom audit pass with only the same three standard axioms. Generated
hashes and the original vendored M sources match the pinned generation inputs.
Table provenance remains the deferred gap.

**Integer-product milestone:** all four selector cases now have an exact integer
product-plus-remainder relation. Each byte column is lifted separately using
lookup-derived limb/byte/carry bounds, then the four equalities are combined.
The shared arithmetic lemma requires `p ≥ 2^29`; the artifact proof also requires
the serialized inverse. Decoder selection and dividend limb bounds remain
interfaces. Four satisfying imported rows cover the maximum 32-bit product,
three nonzero carries and nonzero DIVU/REMU output routing. Full build (3473 jobs),
29 importer checks, changed-module warnings-as-errors and the 72-claim axiom audit
pass with only the three standard axioms.

**Division milestone:** the imported comparison equations and range queries now
prove `remainder < divisor` for nonzero divisors, reusing the shared two-limb
borrow theorem. The integer product relation and Lean's division uniqueness
theorem force DIVU/REMU outputs. One circuit model and shared soundness claim now
cover zero and nonzero divisors against the original Sail clauses, including
native register/PC effects. Dividend/initial-PC bounds, selector identity and
successful native reads remain interfaces; divisor/output bounds and zero flags
are derived. Concrete rows cover zero divisor, a two-limb divisor, a nonzero
remainder, source/destination aliasing and PC carry. A quotient/remainder pair
with remainder equal to divisor is rejected.
Full build (3475 jobs), 29 importer checks, changed-module warnings-as-errors and
the 75-claim axiom audit pass with only the same three standard axioms.

**Native multiplication progress:** MUL/MULHU now share the same circuit model,
selector contract and soundness theorem as DIVU/REMU. Bounded low/high product
halves give unique output selection; the native proof uses Sail's signed low
MUL and unsigned high MULHU clauses. All four actual rows cover native source /
destination aliasing, including a maximum-word product with nonzero carries.
Full build (3475 jobs), 29 importer checks, eight changed modules checked with
warnings-as-errors and 79 audited claims pass with only the same three standard
axioms. M-extension x0 coverage is recorded below.

**M-extension x0 progress:** the existing discarded-write contract and one shared
proof now cover the original Sail MUL/DIV/REM clauses, including all multiplication
sign/half choices and signed/unsigned division. Native state preservation and
PC carry follow from the imported ADD/SUB NOP row; successful original reads and
decoder/NOP binding remain explicit, with no operand bounds or result premise.
The full build, 29 importer checks, changed-module warnings-as-errors and the
79-claim axiom audit pass. Next independent family: shift/binop.

**Shift/binop foundation:** all 52 equations and seven queries are imported into
Clean, retaining dynamic table tags and validating setup/decoder boundaries,
padding, query sets and scratch aliases. Local flags, final-PC range bounds and
PC+4 reuse shared arithmetic; initial bounds and the serialized inverse remain
explicit. Fully satisfying XOR rows exercise a PC limb carry; the first
noncanonical final limb is rejected. Nonzero fixed-table rows cover binops,
sign extension and maximum signed shift. Full build (3485 jobs), 36 importer
checks, nine changed modules with warnings-as-errors and 82 audited claims pass
with only the same three standard axioms. Byte-table setup provenance remains
the existing deferred gap. Next: byte-result reconstruction and shared native
Sail soundness for standard binary/shift operations.

**Binary-operation milestone:** XOR/OR/AND and XORI/ORI/ANDI now share one model
and native Sail soundness claim. Tagged Clean membership forces operand/result
bytes; the imported assembly equations and shared byte-reconstruction lemma
give the destination word. No operand-range assumptions are needed. Decoder
selection, operand-byte interpretation, successful native reads and initial-PC
bounds remain explicit; immediate interpretation uses original Sail sign
extension. The shared native retirement proof supplies register/PC effects,
including source/destination aliasing and no 32-bit PC overflow. Table setup
provenance remains deferred. Six satisfying imported rows cover all six clauses,
immediate -1, a nonzero signed source, source/destination aliasing and PC carry.
Full build (3495 jobs), 36 importer checks, ten changed modules with warnings
treated as errors and 86 audited claims pass with only the same three standard
axioms. Shift reconstruction progress is recorded below.

**Shift reconstruction:** native Clean membership and imported wiring now force
five-bit rs2 truncation and all sixteen contribution bytes. The assembly equations
force SLL/SRL/SRA results for mapped native source bytes, using one shared disjoint
byte proof; no result/scratch bounds are assumed. The generic field bound is
`262144 < p`. The unchanged pinned Sail pipeline now retains original `SHIFTIOP`.
The native architectural connection is recorded below. Table provenance stays
deferred.
Full build (3511 jobs), 36 importer checks, twelve satisfying shift rows, rejection
of count 32, eleven changed modules with warnings treated as errors and the
99-claim axiom audit pass with only the same three standard axioms.

**Native shift milestone:** SLL/SRL/SRA and SLLI/SRLI/SRAI now join the existing
XOR/OR/AND model and shared Sail register/PC soundness theorem. Counts are proved
from the imported truncation query plus operand mapping, matching original
`RTYPE`/`SHIFTIOP`; immediate payload legality remains a decoder interface.
The same `262144 < p` field bound and explicit serialized inverse apply. No
operand/result/scratch ranges are assumed. Immediate x0 shifts reuse ADD/SUB's
shared NOP proof; register shifts were already covered there. Twelve satisfying
shift rows check counts 0/31, register truncation of 32/63, signed input, SRAI
upper encoding bits, source/destination aliasing and PC carry. All six binary
rows still pass. Full build (3511 jobs), 36 importer checks, eight changed modules
with warnings treated as errors and 101 audited claims pass with only
`propext`, `Classical.choice`, `Quot.sound`.

**Native REV8 milestone:** the original upstream Zbb byte loop and `execute_REV8`
are retained through the existing pinned Sail pipeline. Their byte-permutation
lemma feeds the same contribution/assembly proof and shared register/PC soundness
claim. The decoder mapping supplies zero count; no result or scratch bounds are
assumed. REV8 writes to x0 reuse the ADD/SUB NOP proof. Concrete fixtures cover
0x80abcd12 → 0x12cdab80, source/destination aliasing and PC carry; all previous
bitwise/shift checks still pass. Full build (3513 jobs), 36 importer checks, nine
changed proof/review modules with warnings as errors and 104 audited claims pass
with only `propext`, `Classical.choice`, `Quot.sound`. Sail source pins are unchanged;
generated hashes and the unmodified Zbb/arithmetic source copies are checked.
Word memory is the next independent family: imported address/PC equations followed
by explicit ROM/memory interfaces. Table extraction and cryptographic arguments
remain deferred.

**Native branch soundness:** the missing `sys_enable_experimental_extensions`
binding is resolved by an explicit `false` configuration, matching the pinned
emulator's default/getter. The original backend imports our small platform file;
the generator checks the source definitions and records hashes. With unchanged
pins, BTYPE/JAL/JALR now compile. All six standard branches share native Sail
state/PC soundness using the imported condition and PC equations. The shared
retirement rule now handles arbitrary circuit-proved targets. Outcome/alignment
are derived; operand/offset bounds, decoding, initialized native reads (including
arbitrary misa) and the final-PC high bound remain interfaces. Native JAL/JALR
soundness is now checked in the next milestone.
Twelve concrete satisfying rows now check native retirement for all six branch
tags, both outcomes, signed/unsigned disagreement, negative offsets, PC wraparound
and both misa settings. Full build (3529 jobs), 40 importer checks, seven changed
Lean modules with warnings as errors and 122 audited declarations pass with only
`propext`, `Classical.choice`, `Quot.sound`. Fresh generated hashes, platform/adapter
hashes and the unmodified pinned source copies are checked.

**Native jump soundness:** JAL/JALR share one native-state claim using the same
target/link equations and retirement rule. The slice adds the original Zicsr
module so JALR's configuration query uses its real clause rather than the incomplete
pattern fallback. Its landing-pad update is proved inactive from actual Machine-mode
and MLPE-clear CSR reads; other configurations remain outside the claim. The
imported relation forces target alignment, saved links, wrapping and bit-0 cleanup.
Decoder identity, input/offset bounds, final high-PC bounds and initialized native
reads remain explicit. The source and destination may alias; x0 writes are covered.
Eight satisfying imported rows check native JAL/JALR, wrapping links/targets,
negative offsets, odd sums, aliases, x0 and preservation of an initialized elp bit.
Full build (3533 jobs), 40 importer checks, five changed/new Lean modules with
warnings as errors and 126 audited declarations pass with only the standard three
axioms. Fresh generation, file hashes and the pinned Zicsr source copy are checked.

**PC interface gap:** a kernel-checked selected SLTU row satisfies every imported
assertion and lookup with initial PC zero, final low limb four and high limb
`p - 65536`. Canonical limb decoding gives PC 65540 in BabyBear, not four.
The local relation does not supply a final-PC high-limb bound. A global PC-state range
contract is retained in architectural comparison soundness; this counterexample
does not establish acceptance by the full execution/ROM arguments. Input alignment
also belongs to the normal four-byte path's interface. See `Tests/Comparison.lean`.

**PC composition:** shared logical range transfer is checked in
[PCState](Airbender/Review/PCState/Theorems.lean).
The [compiler](../../cs/src/gkr_compiler/memory_like_grand_product.rs) places both
PC limbs and timestamp in the state permutation. The
[decoder table](../../cs/src/gkr_circuits/decoder_trait.rs) splits supported PCs
into 16-bit limbs; the proof excludes unsupported `-1` padding using the low bound.
The [boundary contribution](../../prover/src/definitions/mod.rs) splits the terminal
`u32` PC into bounded limbs as well. One family `final_pc_bounds` theorem derives
the outgoing low bound from imported cleanup queries and supplies the high bound
needed by the comparison/branch/jump soundness interfaces. The malformed local
comparison row is proved incompatible with this logical global contract.
Binding the modeled decoder projection and active state lists to the actual
setup/trace remains open. Cryptographic arguments and setup extraction stay deferred.

Start with jump/branch/SLT while completing independent ADD/SUB custom-interface
work. Extend the shared native Sail interface only for actual imported clauses.
For initialization/teardown, do not mistake an empty richer import for circuit
verification; obtaining an appropriate richer artifact is a generation-input gap.

### Execution rules after plan approval

- Work through the dependencies above; finish independent tasks when another task
  is blocked by unavailable specification or generation inputs.
- Commit coherent verified milestones using messages inferred from the changes.
  Summarize the actual proof coverage, remaining assumptions and checks for each.
- Keep field-specific artifact facts distinct from reusable generic algebra.
- Preserve the strict JSON import, sole Clean constraint model, reused Sail standard
  semantics and the `Review/` versus `Proofs/` versus `Import/` boundary.
- Do not start table extraction, compiled correspondence, cached equivalence or
  cryptographic argument proofs during this coverage pass.

## Deferred milestones

These remain tracked but are outside the next circuit-coverage pass.

1. **Extract fixed lookup tables.** Export rows and table identity from Airbender's
   actual Rust setup generator, then import that artifact into Clean's `StaticTable`
   and prove membership properties over the imported rows. Record generation
   provenance, validate query-to-table binding, and account for zero padding.
   Export/import fidelity and lookup-argument soundness remain separate obligations.
2. Prove correspondence with compiled no-cache gates. Soundness needs compiled
   constraints to imply the richer constraints; equivalence also needs witness extension.
3. Prove cached-layout equivalence, including verifier helper expressions.
4. Discharge the remaining decoder/preprocessing and lookup-setup contracts.
5. Prove lookup-argument and memory-argument soundness; compose row results into
   whole-execution correctness.
6. Establish completeness for each declared circuit relation.
7. Treat verifier implementation refinement and cryptographic protocol soundness
   as separate downstream proofs, connected through explicit interfaces.

## Completion criteria

- Actual imported constraints, arbitrary witnesses and the pinned Sail reference.
- Shared property definitions and reusable lemmas; no copied per-family foundations.
- Explicit assumptions without the desired arithmetic conclusion.
- A compact review entry stating observables, instruction/field coverage and artifact identity.
- Kernel-checked proofs with no `sorry`, admitted project axioms or assumed
  compilation correspondence.
- Honest separation of conditional circuit claims, architectural coverage and
  protocol claims, with import/generation trust boundaries recorded.

## Pins and remaining inputs

- Base revision: `av_gkr_compiler`, `28ffe3ff0353edd9051485c2974b28b52b495dc4`.
- Artifact: `cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json`.
- Artifact SHA-256 (committed bytes): `084a58f08dd122160b548689383f74d4a790c782046f8a5bf43f9f287c22a620`.
- Lean/Mathlib: `v4.31.0`. Clean: `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`.
- Sail model/compiler/runtime pins: [provenance](generated/sail-rv32/provenance.json).
- Authoritative project scope/custom-operation document: [provided specification URL](https://github.com/matter-labs/zksync-airbender/blob/mb_gkr_compiler/spec/top-down/00%20master.md#supported-instruction-set-and-custom-operations).
  [Unmodified local copy](vendor/airbender/00-master.md#supported-instruction-set-and-custom-operations)
  at `2331d1c511f26c17be85879fbab02ab109aefd05`, with [hash/provenance](vendor/airbender/provenance.json).
  Its correspondence with this circuit revision still needs review; standard
  instruction execution continues to use the separately pinned Sail model.
- The actual large-field JSON import/profile remains to be implemented. Generic
  prime-field proofs do not establish that a Proth120 artifact was imported.

Source references: `cs/src/structured_expr.rs`, `cs/src/gkr_circuits/add_sub_family/`,
`cs/src/gkr_compiler/mod.rs`, `field/src/baby_bear/base.rs`, `field/src/proth120.rs`.


**Word-memory foundation:** all 27 retained equations, three range queries and the
conditional ROM query are imported into native Clean. The ROM table is an explicit
caller-supplied nine-column table; program/setup binding remains an interface.
Logical placement resolves the ranges to the separator residue and final-PC limbs.
Shared limb arithmetic proves load/store effective addresses with 32-bit wraparound
and PC+4 without overflow. Source/immediate/address bounds and the serialized inverse
remain explicit; final-PC bounds are derived. Two satisfying RAM rows check load/store
address and PC carries with the disabled-ROM zero query. Full build (3521 jobs),
40 importer checks, seven changed/new modules with warnings as errors and 108 audited
claims pass with only the three standard axioms. Native Sail LW/SW, ROM selection/data
semantics and memory-state projection are the next work; no memory argument is claimed.

**Word-memory routing:** the imported equations select rs2/rd register ports,
classify ROM as addresses below 4 MiB and exclude ROM stores. Eliminating all
data-query copies proves RAM limb transfer under a table-wide zero-tag law and
binds active ROM-load output to native Clean membership at the selected address.
The program/setup table binding remains external; no table extraction is added.
Tests include a satisfying ROM row with unrelated RAM-read placeholders, rejection
of changed RAM data limbs, and exclusion of ROM stores. Full build (3521 jobs),
40 importer checks, four changed modules with warnings as errors and 113 audited
claims pass with only `propext`, `Classical.choice`, `Quot.sound`.

**Native LW/SW:** the original clauses are installed with unchanged pins and bodies.
Terminal/reservation externals are abstract `MemoryPlatform` parameters; the exact
header insertion and original emitter hash are recorded and checked. No platform
implementation or axiom is supplied. RAM LW/SW share conditional native Sail
soundness for effective address, transferred data, GPR effects and PC+4, including
aliases. The decoder's nonzero-LW-destination and SW/no-destination rules remain
explicit; preprocessed x0 loads are separate. Stores reuse the common retirement proof with native memory
writes. Input/address bounds, pre-state read binding, disabled-ROM table behavior
and uniform native translation/access transport remain explicit interfaces.
The full build (3531 jobs), 40 importer checks, warnings-as-errors for ten changed
modules and the 140-declaration axiom audit pass with only the three standard axioms.
The same theorem now covers ROM loads through an independent program-image
binding, quantified over canonically decoded field-valued table rows. RAM read-port
bounds/binding are needed only outside ROM; store exclusion from ROM is derived.
A nonempty program-table fixture proves that image contract against independently
specified native little-endian bytes, including unrelated RAM-read placeholders.
Shared row composition now accepts native memory-write projections.
ROM extension checks: full build (3532 jobs), 40 importer checks, five modules
with warnings as errors and the 140-declaration axiom audit pass with no new axioms.
Next: subword memory; discharge valid-path transport from platform
configuration separately. Table extraction and cryptographic arguments stay deferred.

**Subword local equations:** all 43 retained equations, five ranges and both
non-decoder data queries are imported, with exact source bytes and column guards.
PC+4, cell alignment, unique byte-offset decomposition, halfword alignment,
register routing and ROM/store exclusion are checked. Low-address bounds come
from the local queries; selected high-address and source/immediate bounds stay
explicit. A shared ROM separator lemma replaces duplicated word-memory algebra.
All load widths now reuse one proof of the original Sail LOAD clause. Data-query
copies are eliminated for RAM loads, ROM loads and stores; their table semantics
are the next step, followed by native byte/halfword effects. A satisfying LBU
fixture exercises the clearing and byte-load queries; odd halfword offsets and
misaligned cell addresses are rejected. Native RAM-load coverage is recorded below.
Checks: full build (3538 jobs), 46 importer checks, ten modules with warnings as
errors and 157 audited declarations pass with only the three standard Lean axioms.

**Subword RAM tables:** the tagged setup now symbolically reconstructs the fixed
and ROM rows from their Rust generators, with an independent padded program-word
function. Rust setup correspondence/extraction remain deferred. Selected RAM tags
force canonical keys and output limbs; their signed/unsigned byte/halfword formulas
are proved equal to Sail's actual `extend_value`. Both RAM-load modes derive output
bounds from the imported query. The same complete LBU witness satisfies the full
modeled setup, and sign-boundary fixtures exercise 0x80 and 0x8000. Native RAM-load
coverage follows below. Store-byte clearing/merging, ROM-image binding and native
SB/SH effects follow; no table extraction or rich/gate correspondence is added.
Checks: full build (3542 jobs), 46 importer checks, four changed modules with
warnings as errors and 164 audited declarations pass with only standard Lean axioms.

**Subword RAM instruction soundness:** one shared claim covers LB/LBU/LH/LHU:
aligned read-cell address, byte/halfword extraction, sign extension, destination
register and native PC retirement. Packed keys are bound to the fixed input word;
native subword reads follow from the pinned interpreter's four-byte read. The
read-port premise refers to the address calculated from the source operands.
Input/high-address bounds, decoder modes, successful native reads and uniform
platform transport stay explicit; output bounds and halfword alignment are local
consequences. Store clearing/merging and SB/SH effects, then ROM-image effects,
remain next. Table extraction and richer/gate correspondence stay deferred.
Checks: full build (3550 jobs), 46 importer checks, seven changed modules with
warnings as errors and 170 audited declarations pass with only standard Lean axioms.

**Subword store equations:** the fixed byte-source, byte-clearing and disabled
rows now have checked membership semantics. The imported SB/SH equations uniquely
determine both new limbs, preserve the opposite halfword and derive output bounds.
Complete SB and SH witnesses satisfy all equations and seven queries against the
modeled setup. The native Sail STORE clause now has a shared byte/halfword lemma.
Full SB/SH soundness still needs the connection between the merged cell write and
Sail's native narrow write, followed by retirement; no replacement ISA spec is used.
Checks: full build (3552 jobs), 46 importer checks, six changed modules with
warnings as errors and 180 audited declarations pass with only standard Lean axioms.

**Subword RAM store soundness:** the shared LB/LBU/LH/LHU claim now includes
SB/SH. The merge equations imply the exact byte-window encoding; a native interpreter
proof equates full-cell and narrow writes, including all preserved bytes and GPRs.
Sail STORE and retirement establish the complete memory/PC effects. The old-cell
read is bound to the independently computed operand address. Source/old-word bounds,
decoder modes and uniform platform transport remain explicit; ROM-load effects
and modeled-setup provenance are next/deferred respectively. Complete SB/SH witness
fixtures also check the resulting native writes. Checks: full build (3552 jobs),
46 importer checks, seven changed modules with warnings as errors and 184 audited
declarations pass with only the three standard Lean axioms.

**Subword ROM soundness:** the same shared theorem now covers ROM LB/LBU/LH/LHU
alongside RAM loads and stores. Membership uniquely decodes packed address/sign/
position fields and fixes the exact slice of the independent padded program word;
Sail supplies extension and native retirement. The RAM-only restriction is removed.
A uniform program-image/native-memory binding remains explicit. Packed keys require
`p > 2^25`; coefficient compatibility remains separate. Complete signed ROM-byte
and ROM-halfword witnesses satisfy all equations/lookups. Table extraction, Rust
setup binding and lookup/memory argument soundness remain deferred. Checks: full
build (3554 jobs), 46 importer checks, six changed modules with warnings as errors
and 186 audited declarations pass with only standard Lean axioms.

**Unified foundation:** all 129 retained equations, 13 ranges and five ten-column
pooled queries are imported into Clean with setup/column guards. Boolean controls
and active dispatch exclusivity are proved; the auxiliary rd-zero marker is excluded
from the dispatch sum. Both final-PC bounds are local, and ordinary rows advance
PC+4 without overflow under bounded initial limbs and `p > 131072`. A complete
satisfying row exercises the PC low-limb carry. Full build (3560 jobs), 53 importer
checks, seven modules with warnings as errors and 192 audited declarations pass
with only standard Lean axioms. Native instruction soundness is next; pooled setup
semantics and decoder binding remain interfaces, with extraction still deferred.

**Unified standard arithmetic:** ADD/ADDI/SUB/LUI/AUIPC now share native Sail
register/PC soundness, including aliases and x0 preprocessing. Only the selected
operation is assumed; the local dispatch proof excludes all others. Standalone
and unified proofs reuse one limb calculation and decoder-preprocessing definition.
The generic premise is `p > 196608`, without an inverse identity or setup-table
behavior premise. Complete ADD/ADDI-x0 witnesses and a rejected two-selector row
check artifact attachment and native effects. Full build (3566 jobs), 53 importer
checks, ten modules with warnings as errors and 197 audited declarations pass
with only standard Lean axioms. The initial high-PC bound is now also derived
through canonical mapping and its imported range query, leaving only the low-PC
bound assumed. The full build, four strict-warning modules and 198-declaration
axiom audit pass after that reduction. Next: remaining unified branches and the
delegation families; TRIADD can reuse three-word addition, and Clean already
provides the G mixing-function reference needed by BLAKE2s/BLAKE3.

**Unified TRIADD:** MOP.RR.4 has shared soundness against the pinned project
operation and native Sail register/PC effects, including three-way aliases and
x0 preprocessing. One word-addition lemma now handles carry sums up to two;
existing standard, memory and control-flow callers reuse it. Output/high-PC ranges
and selector exclusivity are local; source/old-word bounds and native reads remain
interfaces. Complete maximal-operand and x0 witnesses check the imported relation
and native effects. Full build (3570 jobs), 53 importer checks, fourteen strict-
warning modules and 202 audited declarations pass with only standard Lean axioms.
Next: BLAKE2s G-function import and proofs against Clean's existing G definition,
then remaining unified/delegation branches. Table extraction and compiler proofs
remain deferred.

**Sail runtime compatibility:** the missing runtime-error instance inside early
returns is implemented over Sail's existing effects. Kernel proofs establish fault
propagation and equivalence with its native error handler after removing early
returns. Regeneration preserves all instruction/support output except the copied
platform file, with unchanged pins. Rechecking the LW/SW slice removes the
`MonadExcept` and experimental-extension errors. Full build, 40 importer checks,
warnings-as-errors and the 127-declaration axiom audit pass with no new axioms.
