# Shift/binop review guide

Start with [the original-constructor projection](Decoder.lean), [literal native
export/public fixture](NativeData.lean), then the [short data certificate](../../Trace/Families/ShiftBinop/NativeDecoder.lean).
The certificate covers twelve ordinary register/immediate forms, their original
x0 variants, an unsupported ADD hole and every native decoder row.

[Internal assembly](../../../Proofs/ShiftBinop/NativeSetup.lean) reads public
bytes, runs original Sail decoding and proves the actual compressed padding
structurally through [the constant-tail helper](../../../Proofs/Tables/ConstantTail.lean).
[Concrete regressions](../../../../Tests/ShiftDecoder.lean) check original x0,
full 16-bit signed immediate limbs, SRAI funct7 payload and unsupported forms.
[Strict importer regressions](../../../../Tests/ArtifactImport.lean) keep the
native profile separate from arithmetic/control exports.

The sections below preserve the successive decoder/table checkpoints. The current
[routing claim](Routing.lean) binds all four table tags and operand selection to
original public decoding; [lookup claims](Lookups.lean) connect the complete native
dynamic import to exact helper membership and derive all selector domains.
[The binary result claim](Binary.lean) now proves exact selected XOR/OR/AND words
and actual x0 writes with derived operand bounds. [The shift contribution claim](Shifts.lean)
derives exact canonical-key contributions and selected-word assembly. [Initialized history](../../Trace/Families/ShiftBinop/History.lean)
now derives native clocks and latest reads from original public seeds and matching.
[Initialized word ranges](../../Trace/Families/ShiftBinop/Values.lean) and
[canonical source keys](../../Trace/Families/ShiftBinop/Sources.lean) are now derived. [Whole numerical results](../../Trace/Families/ShiftBinop/Theorems.lean)
are now checked. [Actual Sail GPR/cell transport](../../Trace/Families/ShiftBinop/Registers.lean)
is now derived. Original instruction execution, custom CSR/oracle
semantics and physical cryptographic enforcement remain unfinished. General
Rust/JSON/compiler refinement is a separate boundary.

## Native binary table prerequisite

[Two short helper claims](../../Helpers/Tables/NativeBinary.lean) now connect actual native XOR/OR/AND rows to original Clean membership and bytewise semantics, retaining the actual conditional zero row and native offsets. [Internal assembly](../../../Proofs/Tables/Binary.lean) reuses full literal-block source output certificates and structural geometry; [regressions](../../../../Tests/NativeBinary.lean) check complete native data and reject malformed keys/results. This does not import the compiled circuit: dynamic selectors, large 16-bit shift tables, custom CSR/oracle semantics and initialized family execution remain unfinished.

## Native shift scalar and sign-fill tables

[The short helper claims](../../Helpers/Tables/NativeShiftScalars.lean) now connect actual native truncation, zero-padded range and every sign-fill row to original Clean membership and exact results, including negative shift zero. [Internal assembly](../../../Proofs/Tables/ShiftScalars.lean) uses structural constant-block geometry across 64 symbolic domains and independent RV32 mask arithmetic. [Regressions](../../../../Tests/NativeShiftScalars.lean) check boundary cases and malformed queries. Native compiled offsets retain unexported regions. The four large logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SRL rows

[Two short helper claims](../../Helpers/Tables/NativeSrlLow.lean) identify actual native SRL-low membership with original Clean semantics and derive bounds, zero high output and exact RV32 logical shift for all 2,097,152 rows. [Internal assembly](../../../Proofs/Tables/SrlLow.lean) reuses the source block checker with six symbolic actual-block certificates and independent bitvector arithmetic. [Regressions](../../../../Tests/NativeSrlLow.lean) cover shift/final-bit boundaries and malformed queries. The other three logical-shift tables, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SLL rows

[Two short helper claims](../../Helpers/Tables/NativeSllHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SLL rows and derive bounds, zero low output and exact wrapped RV32 shift. [Internal assembly](../../../Proofs/Tables/SllHigh.lean) uses six symbolic actual-block partitions, ten checked stored templates and independent bitvector arithmetic. Generic size/output proofs avoid imported-data normalization under unchanged ceilings. [Regressions](../../../../Tests/NativeSllHigh.lean) cover discarded/final bits, shift boundaries and malformed queries. Low-input SLL, high-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native low-input SLL rows

[Two short helper claims](../../Helpers/Tables/NativeSllLow.lean) connect original Clean membership to all 2,097,152 actual low-input SLL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SllLow.lean) reuses the complete native SLL-high low column and a checked 73-block high suffix, with six symbolic native carry partitions. [Regressions](../../../../Tests/NativeSllLow.lean) cover first carry, shifts sixteen/31, surviving/discarded bits and malformed queries. High-input SRL, dynamic constraint import and initialized family execution remain unfinished.

## Native high-input SRL rows

[Two short helper claims](../../Helpers/Tables/NativeSrlHigh.lean) connect original Clean membership to all 2,097,152 actual high-input SRL rows and derive both limb bounds and exact reconstructed RV32 shifts. [Internal assembly](../../../Proofs/Tables/SrlHigh.lean) reuses native SRL-low for the entire high column and a 73-block low suffix, retaining all 146 low blocks, ten rotated templates and five symbolic prefix certificates. [Regressions](../../../../Tests/NativeSrlHigh.lean) cover cross-shift/reset edges, shifts sixteen/31, final bits and malformed queries. All four native logical-shift limb tables now have helper membership/results; dynamic constraint import and initialized shift/binop execution remain unfinished.

## Complete native dynamic lookup import

[The local artifact](Artifact.lean) now retains all fifty equations, eight timestamp
queries, the four actual witness selectors and complete native state/port/setup
metadata. [The actual tagged table](Tables/Native.lean) spans all twelve compiled
regions and 10,817,537 rows; [structural proofs](../../../Proofs/ShiftBinop/NativeLookup.lean)
retain every stored row. [Regressions](../../../../Tests/ShiftArtifact.lean) check
selector evaluation, all native metadata and explicit profile rejection.

The [CSR data](Tables/NativeCsrData.lean) uses the exact compilation-test profile:
nondeterminism enabled, empty delegation CSR list. Proving-time CSR setup binding,
custom CSR/oracle/delegation behavior, numerical family soundness and initialized
shift/binop Sail execution remain separate. Import fidelity is not a compiler
refinement proof. All previous native helper claims retain their checked scope.

## Accepted tagged-query resolution

[Short public claims](Lookups.lean) extract all four actual queries and their
canonical selectors from native Clean acceptance. [Structural partition](../../../Proofs/ShiftBinop/NativeRegions.lean)
covers every stored region and proves tag uniqueness; [resolution](../../../Proofs/ShiftBinop/NativeResolution.lean)
connects selected rows to the existing binary/scalar/logical-shift helper proofs.
Tag zero requires three zero fields. [Regressions](../../../../Tests/ShiftLookups.lean)
check valid boundaries, malformed values/tags, crossed SLL regions and field wrap.
Runtime CSR binding, operation routing and initialized family execution remain
separate. These files are task-authored v2 assembly over the already pinned data
and helper interfaces; they add no source-v3 coverage claim.

## Original public decoding and operation routing

[The short public claim](Routing.lean) derives ordinary native routing from actual
public-byte construction, native decoder membership and accepted constraints.
[References and observables](RoutingModel.lean) keep the six-bit mask, distinct
funct3 and actual four-slot order visible. [Internal assembly](../../../Proofs/ShiftBinop/Routing.lean)
derives the table tags, register/immediate operand selection and zero ordinary
request multiplicity. SRA routes truncation/sign-fill/SRL-low/SRL-high; SRAI keeps
its native funct7 immediate bits. [Complete native rows](../../../../Tests/ShiftRouting.lean)
cover all twelve forms and x0 variants, with checked original public routing and
malformed-tag/operand/CSR-bit rejection. Numerical word results, actual Sail
register reads, initialized family execution and delegation protocol soundness
remain unfinished.

## Native XOR/OR/AND results

[The short public numerical claim](Binary.lean) derives both operand bounds,
the selected RV32 operation and actual x0-masked writes from original public
construction, native decoder membership and accepted constraints.
[References](BinaryModel.lean) retain actual native word observations.
[Query assembly](../../../Proofs/ShiftBinop/BinaryQueries.lean) uses all four byte
lookups and the native inverse-256 equations. [Word assembly](../../../Proofs/ShiftBinop/BinaryValues.lean)
preserves full 32-bit values above Mersenne31; [masking and source assembly](../../../Proofs/ShiftBinop/BinaryResults.lean)
derive original decoded x0 behavior. [Regressions](../../../../Tests/ShiftBinary.lean)
cover all twelve binary register/immediate/x0 forms and corrupted byte/result/write
rejections using complete accepted native fixtures. Native shifts, initialized
register/history transport, original Sail execution and runtime CSR binding remain
unfinished. Earlier sections retain their checkpoint scope.

## Native shift contributions

[The short public contribution claim](Shifts.lean) derives native truncation,
exact bounded SLL/SRL/sign-fill contributions and actual selected-word assembly
from original public decoding and accepted native constraints.
[References](ShiftModel.lean) expose canonical packed keys and native slot/source
order. [Actual equations](../../../Proofs/ShiftBinop/ShiftEquations.lean) bind keys
and selected sums; [table resolution](../../../Proofs/ShiftBinop/ShiftParts.lean)
retains all checked native helper results and literal inactive zero slots.
[Internal selected assembly](../../../Proofs/ShiftBinop/ShiftContributions.lean)
lifts both three-limb sums without field wrap. [Regressions](../../../../Tests/ShiftContributions.lean)
cover all twelve shift register/immediate/x0 cases, SRAI 1055→31, native sign-fill
order, shift-31 boundaries and malformed key/inactive/missing-fill rejection.
Canonical packed-key source binding needs initialized bounded reads before
claiming architectural shifts; family clocks/history and original Sail execution
remain unfinished. Earlier sections retain their checkpoint scope.

## Native initialized clock and memory connection

[The short trace history claim](../../Trace/Families/ShiftBinop/History.lean)
binds the native port/clock metadata through the [family registry](../../Helpers/Context/ShiftBinop.lean).
[Native clock proofs](../../../Proofs/ShiftBinop/Timestamp.lean) use both actual
carry equations and all eight timestamp queries. Original Sail public seed/PC
reads and native matching derive every local/prior clock input and complete
Clean history. [All twenty-four initialized native cases](../../../../Tests/ShiftHistory.lean)
retain actual destination masks and readonly x0 refreshes; all six stale
immediate/x0 variants fail logical memory matching while passing local equations.
Source-word bounds, packed-key binding and original Sail cell/instruction
execution remain the next connections. Earlier sections retain their scope.

## Initialized ranges and canonical source keys

[The public range claim](../../Trace/Families/ShiftBinop/Values.lean) derives every
native read/write/terminal bound through unchanged initialized time induction.
[The public source claim](../../Trace/Families/ShiftBinop/Sources.lean) derives
actual natural packed-key values, source remainders, amount quotients and bounded
selected limbs. [Source observables](SourcesModel.lean) expose only native columns
and conclusions. [Internal lifting](../../../Proofs/ShiftBinop/ShiftSourceBounds.lean)
retains actual contribution semantics and separately checked SLL/SRL/SRA half
non-overlap across all 32 amounts. [Regressions](../../../../Tests/ShiftValues.lean)
apply both initialized claims to complete ordinary/x0 histories and all twelve
shift cases. Whole architectural shifts and Sail cell/instruction execution remain
separate; older sections retain their checkpoint scope.

## Initialized whole numerical results

[The short public trace claim](../../Trace/Families/ShiftBinop/Theorems.lean)
now derives exact canonical selected and actual write limbs for every ordinary
shift/binop family, including immediate and x0 forms. [References](ResultsModel.lean)
use whole RV32 shifts and low-five-bit amounts. Separate whole-limb
[SLL](../../../Proofs/ShiftBinop/SllLimbResult.lean),
[SRL](../../../Proofs/ShiftBinop/SrlLimbResult.lean) and
[SRA](../../../Proofs/ShiftBinop/SraLimbResult.lean) calculations preserve native
piece order, all 32 amounts and both sign domains under default budgets.
[Native result assembly](../../../Proofs/ShiftBinop/Results.lean) derives
canonical outputs and exact decoded x0 masking; [initialized assembly](../../../Proofs/Trace/Families/ShiftBinop/Results.lean)
derives the source bounds. [Twenty-four complete regressions](../../../../Tests/ShiftResults.lean)
check concrete whole results and all discarded writes. Actual Sail cell/GPR and
instruction execution remain next; older sections retain their checkpoint scope.

## Original initialized Sail register transport

[The short public history claim](../../Trace/Families/ShiftBinop/Registers.lean)
derives original Sail source/old-destination reads, actual masked writes, all
segment states and code/misa frames from original public initialization and full
native matching/decoding. [Observables](../../Helpers/Memory/ShiftBinop.lean)
retain the common pre-state and actual native three-port order. [Port transport](../../../Proofs/ShiftBinop/PortReads.lean)
reuses the three original pinned declarations unchanged; [native x0 preservation](../../../Proofs/Trace/Families/ShiftBinop/ZeroRegister.lean)
and shared cell-history realization derive all intermediate states.
[Complete regressions](../../../../Tests/ShiftRegisters.lean) reach actual original
Sail numerical writes for all twenty-four ordinary/x0 forms; all twelve x0
variants preserve the whole data state. Original instruction clauses and PC/fetch
execution remain next; earlier sections retain their checkpoint scope.
