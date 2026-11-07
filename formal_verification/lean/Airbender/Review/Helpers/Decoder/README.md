# Decoder helper review

[Columns](Columns.lean) describes v2's ten native decoder columns, including the
separate destination-zero flag and already-packed family mask. The
[native query](NativeData.lean) preserves DecoderTableEntry.flatten order: two PC
limbs, rs1/rs2/rd, rd-is-zero, two immediate limbs, funct3 and mask.

[Import resolution](../../../Import/Parse.lean) uses the native state descriptor's
memory/witness bank choice, group extents and unique physical-to-logical mapping.
[Mechanical ADD/SUB binding](../../../Proofs/AddSub/ArtifactChecks.lean) fixes the
consumed IDs. The importer rejects unsupported nonempty funct7/family descriptor
fields rather than dropping them. The native preprocessor and padding sources
are pinned in [provenance](../../../../artifacts/provenance.json).

[Regression](../../../../Tests/NativeDecoderMetadata.lean) checks the full query
order. [Public program construction](Program.lean) reads actual Sail bytes and invokes
the pinned original decoder for ADD/ADDI/SUB/LUI/AUIPC. The selected-profile
[logical setup](Setup.lean) retains a power-of-two native-shaped capacity and
its complete all-minus-one tail. Missing, unsupported or effectful entries fail.
General Rust generation/export fidelity remains separate; this is not an imported
physical setup artifact or coverage of mixed/custom-opcode programs.

[Decoder recovery](../../../Proofs/Trace/DecoderSetup.lean) combines actual native
equations with logical membership over that full padded table. The packed-mask
bound excludes padding, then actual public Sail source evidence and the zero flag
are recovered. No table-equivalence or expected per-row metadata premise is used.
Cryptographic enforcement of membership remains separate. V2 keeps original opcode masks and operands when rd=x0;
only the destination write is masked. The local row interface preserves this.
When constructing public tables, retain raw opcode funct3 bits even for U-type
instructions and native minus-one padding; the source's nine-column projection
cannot be copied unchanged.

[Word-memory decoding](WordMemory.lean) uses the same generic original-byte/Sail
construction for LW/SW, with its own native registry and complete minus-one tail.
It retains sign extension, funct3=2, original x0 loads and the separate zero flag.
The [word-memory proof](../../../Proofs/Trace/Families/WordMemory/Decoder.lean)
rejects padding using the native Boolean store mask, then derives actual source
evidence, exact zero flags and PC/immediate bounds/alignment. A local native row
with flag 2 is rejected by full decoder membership. This is not yet initialized
word-memory execution or a public ROM-byte binding.

Successful construction also retains its exact indexed PC sequence. The
[PC composition](../../../Proofs/Trace/PC.lean) derives all incoming bounds and
alignment through RV32 truncation before applying native carry/wrap equations.

[Original clause selection](Instruction.lean) copies the pinned memory/register
dispatcher, selecting original Sail LOAD/STORE clauses. The v3 discarded-load
profile and its exclusions are omitted: v2 original LW-to-x0 memory behavior is
retained. [Native word-memory row assembly](../../../Proofs/Trace/Families/WordMemory/Execution.lean)
now uses actual decoding to select checked preparation/clause/retirement paths;
all calculations remain under Proofs. General finite trace/fetch composition
and physical setup/export remain separate.

[Setup placement](../Tables/SetupColumns.lean) now imports and guards the ten-wide
physical decoder group at column 2 for arithmetic or 6 for word-memory, with
native capacity 2^20 in a 2^24-row setup trace. Tagged generic tuples occupy
word-memory columns 2..5, including the native table ID. This checks compiled
placement; actual Rust-generated decoder columns, unsupported-slot materialization
and physical export/argument fidelity remain separate.

[Sparse construction](SparseSetup.lean) also retains unsupported pure words as
indexed holes. Missing bytes/effectful decoding fail; supported PCs remain 4*i.
[The word-memory interface](WordMemorySparse.lean) reuses the original projection.
[Calculations](../../../Proofs/Trace/Families/WordMemory/SparseDecoder.lean) derive
hole/tail exclusion from native equations and recover actual Sail sources,
canonical words/alignment and the exact zero flag. The [actual interior-hole export](../../Circuits/WordMemory/Tables/NativeSparseData.lean)
has a [complete kernel certificate](../../../Proofs/WordMemory/NativeSparseSetup.lean)
from original public bytes. [Public claims](../../Trace/Families/WordMemory/SparseDecoder.lean)
remain short. [Sparse initialized execution](../../Trace/Families/WordMemory/SparseExecution.lean)
now derives actual construction evidence internally and reuses the strict
history/retirement/terminal assembly. Original slots, PCs and bytes remain intact.
General Rust decoder agreement and full physical setup/argument correspondence
remain separate.

[Actual native arithmetic data](../../Circuits/AddSub/Tables/NativeSetupData.lean)
now reuses this generic sparse constructor. Its [complete certificate](../../../Proofs/AddSub/NativeSetup.lean)
checks every exported row against original Sail public bytes, with signed ADDI,
original SUB-to-x0, raw U-type funct3 and a supported word after an interior hole.
Native packed-mask equations exclude both hole/tail sentinels; [the source claim](../../Trace/Families/AddSub/NativeDecoder.lean)
adds no table-equivalence premise. This concrete export does not establish general
Rust decoder agreement or custom MOP semantics.

[Arithmetic sparse membership](ArithmeticSparse.lean) now feeds the
[short initialized execution claim](../../Trace/Families/AddSub/SparseExecution.lean).
[Proof-internal evidence](../../../Proofs/Trace/ProgramImage.lean) is derived from
actual strict/sparse construction, including original bytes, pure decoding and
indexed PC locations. Native mask equations reject unsupported slots before the
same arithmetic history/retirement/terminal assembly runs. The physical sparse
table keeps all holes/tail; its supported list is only an internal proof index.
General Rust/export and physical argument correspondence remain separate.

[The complete active decoder domain](../Tables/NativeDecoder.lean) now extends
actual native prefixes with the actual native minus-one padding API row. A
literal-data certificate proves repeated filler adds no query, retaining every
active row and excluding final normalization. [The arithmetic execution bridge](../../Trace/Families/AddSub/ActiveSetup.lean)
uses that membership directly; native mask equations still reject sentinels.
General Rust trace/export/LDE and cryptographic enforcement remain separate.

[Control decoding](../../Circuits/JumpBranchSlt/Decoder.lean) reuses sparse public
construction with v2's five packed masks and ten-column native query. Original
SLT/SLTI and jumps to x0 remain intact; SLTI uses mask 8, branches 16, and JAL
retains raw encoding funct3. [Native calculations](../../../Proofs/JumpBranchSlt/Decoder.lean)
exclude all sentinels before recovering original Sail source fields, canonical
words/alignment and the exact zero flag, then derive outgoing PC bounds without
a supplied mask. [The public-byte fixture](../../../../Tests/JumpDecoder.lean)
uses JAL -4 with tag 7, an UNIMP hole and original SLTIU-to-x0. [Actual native export](../../Circuits/JumpBranchSlt/Tables/NativeSetupData.lean)
now has a [complete independent Sail certificate](../../../Proofs/JumpBranchSlt/NativeSetup.lean).
Every prefix/tail row matches the public construction, feeding the short exported
source/PC claim without a table-equivalence premise. General Rust decoder agreement,
initialized control execution and physical argument refinement remain open.

[The control membership interface](Control.lean) keeps full sparse Unit-setup
membership in the separate native control registry. Public original-byte
construction derives supported masks and zero flags for [initialized ranges](../../Trace/Families/JumpBranchSlt/Values.lean);
actual address/query equality and native masks supply x0 preservation for
[Sail cell histories](../../Trace/Families/JumpBranchSlt/SailHistory.lean).

[Initialized control register access](../../Trace/Families/JumpBranchSlt/Registers.lean)
uses these original public source entries and native query indices to select both
Sail source reads, the old destination read and actual masked write. The states
come from shared native history segmentation; original instruction clauses and
PC/operation semantics remain a separate connection.

[The native jump-link claim](../../Circuits/JumpBranchSlt/Theorems.lean) uses full
public construction/membership to derive both PC bounds and the exact x0 flag.
Masks one/two classify native JAL/JALR; packed native equations recover selectors.
The public caller supplies no local range, carry, zero flag or desired link.

[Initialized jump targets](../../Trace/Families/JumpBranchSlt/Targets.lean) also
consume actual original decoding to derive JAL offset parity and exact JAL/JALR
identity. The unchanged [original Sail decoder proof](../../../Proofs/Sail/Decoder.lean)
checks the interpreter's appended zero bit; native metadata and full query
membership transport it to the actual immediate. Source bounds come separately
from initialized matching. Original instruction execution/retirement remains open.

[Initialized comparisons](../../Trace/Families/JumpBranchSlt/Comparisons.lean)
use actual original decoder metadata to derive register/immediate mask identity,
signed/unsigned funct3 and the exact x0 flag. Initialized matching supplies native
operand bounds; no local selector, sign/borrow bit or desired result is supplied.
Original Sail instruction execution/retirement and branch semantics remain open.

[Comparison PC advancement](../../Trace/Families/JumpBranchSlt/ComparisonPC.lean)
uses full original public decoder membership to derive incoming PC bounds,
alignment and register/immediate comparison identity. Native equations and both
candidate scalar queries determine PC+4 with RV32 wrap. This PC-only claim needs
no register-image boundary and supplies no desired PC or final-high closure.
Original instruction retirement and branch semantics remain separate.

[Initialized branches](../../Trace/Families/JumpBranchSlt/Branches.lean) now
derive the native mask sixteen selector and original funct3 tags 0/1/4/5/6/7
from actual public bytes/decoding. Full native matching supplies both register
word bounds. Native subtraction/inverse/positive-flag equations and actual fixed
membership determine every condition; no caller-supplied equality/sign/borrow
bit or desired answer is used. Branch targets and original Sail retirement
remain separate.

[Initialized branch targets](../../Trace/Families/JumpBranchSlt/BranchTargets.lean)
reuse the original successful Sail decoder's implicit zero offset bit and its
unchanged sign-extension proof. Complete native query membership connects that
parity to actual immediate columns 9/10; public metadata also derives incoming
PC/offset bounds and alignment. Native routing/carries/ranges determine the final
PC from the checked branch condition, with no supplied parity or closure premise.
Original Sail instruction retirement remains separate.

[Original comparison retirement](../../Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
now uses exact native mask four/eight and original SLT/SLTU/SLTI/SLTIU constructor
evidence to select the pinned Sail clauses. Full query columns recover indices,
canonical immediate sign extension and x0; initialized history supplies reads
and writes, while native results/PC proofs supply outputs. Original x0 decoding
is retained through actual source reads, discarded writes and retirement.
General fetched control composition and jump/branch CSR effects remain separate.

[Original branch retirement](../../Trace/Families/JumpBranchSlt/BranchExecution.lean)
now recovers the exact original BTYPE constructor, source indices, sign-extended
offset and six funct3 tags from public decoding/native query membership. Native
matching supplies both source words and their bounds; native target proofs
supply the final PC. The public misa entry is transported by unchanged history
frames, without per-row desired reads, decisions, states or PCs. Full fetched
control composition and original jump CSR effects remain separate.

[Original jump retirement](../../Trace/Families/JumpBranchSlt/JumpExecution.lean)
recovers exact original JAL/JALR constructors, indices, sign extension and
native masks one/two while retaining JAL's raw funct3 bits. Native link/target
proofs and actual history derive all remaining row inputs. Real initial CSR
profiles are transported through history; no per-row desired read, link,
target or after-state is supplied. Full fetched control composition remains open.

[Complete fetched control execution](../../Trace/Families/JumpBranchSlt/Execution.lean)
now replays original public decoding at each constructed state. Actual native
register-space metadata and initialized GPR history preserve all public code
bytes; successful setup construction provides the unchanged pure original
decoder equation. Public constructors dispatch to existing comparison, branch
and jump retirement. The shared composer derives the full finite execution
and native terminal matching under the explicit initial CSR profile. No
intermediate source evidence, desired steps or terminal closure is supplied.
The reversed two-row JAL/JALR regression is a logical native trace, with no
new Rust program-export certificate. General compiler refinement remains open.

## Stateful extension-dependent decoding

[Stateful setup](StatefulSetup.lean) reuses the original Sail interpreter on the public state and keeps sparse indexed holes and the complete native tail. The [unsigned MUL/DIV registry](../../Circuits/MulDiv/Decoder.lean) retains all native masks/tags and original x0 operations. Missing bytes and decoder errors reject construction; unsupported successful results become holes. The unchanged original decoder-frame proof establishes state preservation and replay under the same misa.

## Original decoder replay through MUL/DIV history

[Actual native GPR history](../../Trace/Families/MulDiv/Registers.lean) preserves public bytes and misa, then invokes the unchanged original decoder frame. [The alias-prefix regression](../../../../Tests/MulDivRegisterChain.lean) obtains original decoding after a real earlier write, without supplied replay or intermediate-state premises.

## Stateful original decoding through complete MUL/DIV execution

[The complete public trace claim](../../Trace/Families/MulDiv/FetchedExecution.lean) replays actual original decoding after native GPR history and PC bookkeeping. [Internal composition](../../../Proofs/Trace/StatefulComposition.lean) uses the unchanged source decoder-frame theorem and actual misa preservation, without a pure certificate, extra ISA-read or supplied replay premise.

## Native v2 shift/binop decoder fidelity

[The original constructor projection](../../Circuits/ShiftBinop/Decoder.lean) retains native v2 x0, full immediate limbs and SRAI funct7 bits. [The short data certificate](../../Trace/Families/ShiftBinop/NativeDecoder.lean) connects independent original public reads/decoding to every actual exported row; [internal assembly](../../../Proofs/ShiftBinop/NativeSetup.lean) checks the stored sentinel tail structurally. This finite fixture certificate leaves dynamic table constraints, initialized shift/binop execution and custom CSR/oracle semantics open.

## Native shift/binop initialized membership

[The shift/binop interface](ShiftBinop.lean) uses the actual imported ten-column
query and complete sparse/padded public setup. [Initialized native ranges](../../Trace/Families/ShiftBinop/Values.lean)
and [canonical packed source keys](../../Trace/Families/ShiftBinop/Sources.lean)
now consume this membership and actual public construction. Native constraints
exclude unsupported/sentinel rows and original decoding supplies operation masks
and x0 flags; no local field/range or table-equivalence premise is added.

## Actual native reduced shift profile

[Complete selected-profile membership](ReducedMachine.lean) uses the regenerated
reduced registry's actual ten-field query and the original Sail public sparse
constructor. [The projection](../../Circuits/ReducedMachine/Decoder.lean) retains
native masks, original rd/x0/source fields and encoded SRAI immediates.
[Native packing proofs](../../../Proofs/ReducedMachine/NativeShiftDecoder.lean)
exclude holes/tail; [the short trace claim](../../Trace/Families/ReducedMachine/Decoder.lean)
derives the selected entry and actual fields without supplied selectors or
source values. Native Rust preprocessing exports, general public fixed-ROM
correspondence, other profiles and initialized execution remain separate.

## Actual native reduced arithmetic profile

[Arithmetic membership](ReducedMachineArithmetic.lean) retains every actual native
row query and the complete original public sparse/padded setup. [Projection](../../Circuits/ReducedMachine/ArithmeticDecoder.lean)
keeps the five original arithmetic/x0 constructors, ADDI sign extension and raw
U-type funct3. [The short source claim](../../Trace/Families/ReducedMachine/ArithmeticDecoder.lean)
derives actual masks/indices/zero/immediate fields; native Boolean packing excludes
holes/tail. [Initialized numerical values](../../Trace/Families/ReducedMachine/ArithmeticResults.lean)
derive all range prerequisites, not pre-row Sail GPR or clause execution. Universal
native public preprocessing/ROM/physical setup fidelity remains separate.

## Mixed native reduced supported profiles

[Common full membership](ReducedMachineSupported.lean) uses one [original projection](../../Circuits/ReducedMachine/SupportedDecoder.lean)
for selected shifts and ADD/ADDI/SUB/LUI/AUIPC. [The public source claim](../../Trace/Families/ReducedMachine/SupportedDecoder.lean)
derives entries/actual queries; internal profile transport retains every original
field and native packing excludes holes/tail. [Mixed execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now derives common ranges, native Sail row states and original stateful decoder
replay. No per-row profile or read/result/state answer is supplied. General native
public preprocessing/ROM/physical fidelity remains separate from modeled membership.

## Actual reduced original bitwise projection

[Complete bitwise sparse/padded membership](ReducedMachineBitwise.lean) uses
[original constructors and native fields](../../Circuits/ReducedMachine/BitwiseDecoder.lean).
[Public source recovery](../../Trace/Families/ReducedMachine/BitwiseDecoder.lean)
derives rs/rd/x0/immediate/mask/tag; native Boolean packing excludes padding.
[Common support](ReducedMachineSupported.lean) now includes shifts/arithmetic/bitwise.
This is a logical original decoder contract, separate from native Rust export,
preprocessing/ROM and physical setup enforcement.

## Original reduced comparisons

[ComparisonDecodedTrace](ReducedMachineComparison.lean) is complete original
byte/stateful sparse/padded membership for SLT/SLTU/SLTI/SLTIU. [Source recovery](../../Trace/Families/ReducedMachine/ComparisonDecoder.lean)
derives actual65/67mask,2/3funct3,rs/rd/x0 and sign-extended immediate; native
Boolean packing excludes holes/tail. This remains separate from native Rust
decoder export, ROM/preprocessing/physical enforcement and mixed-profile execution.

[Common supported membership](ReducedMachineSupported.lean) now admits comparisons
as well as shifts/arithmetic/bitwise. [Profile recovery](../../../Proofs/ReducedMachine/NativeSupportedDecoder.lean)
derives the original instruction and exact native query for each admitted profile.
[Common fetched execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
uses that recovered evidence across interleaved rows. This supersedes the earlier
comparison-only scope; native export/ROM/preprocessing/physical fidelity remains separate.

[Native branch mask70 selector recovery](../../../Proofs/ReducedMachine/NativeBranchSelectors.lean)
is now checked locally from actual Boolean assertions and packed112. Original
branch public byte/stateful projection and complete sparse membership recovery
remain open; branches are not yet admitted by the common supported projection.

[Actual branch condition/PC calculations](../../../Proofs/ReducedMachine/NativeBranchPC.lean)
now derive numerical effects internally; original branch fields, PC/offset bounds,
alignment and offset parity still require full public byte/stateful sparse decoder
recovery. The common supported projection continues to exclude branches.

[BranchDecodedTrace](ReducedMachineBranch.lean) now supplies full original branch
sparse/padded membership. [Public recovery](../../Trace/Families/ReducedMachine/BranchDecoder.lean)
derives all ten actual native fields; original stateful Sail decoding derives
offset parity without a public parity answer or constructor filter. Logical
membership remains separate from native Rust export/ROM/physical fidelity.

[Branch original fetched execution](../../Trace/Families/ReducedMachine/BranchFetchedExecution.lean)
now derives original stateful decoder replay in actual native-clock row states,
then retained BTYPE execution at the actual prepared PC. Full source membership
and initialized history discharge both source bounds, alignment and decoded parity.
The public initial Sail state makes misa readable, with unrestricted value; every
local CSR read is derived. Common mixed support still excludes branches pending
operation-specific PC integration. Logical decoding is not native ROM/export or
physical setup certification.

[Common supported membership](ReducedMachineSupported.lean) now admits branches
with exact original fields/query transport. SupportedISA is a public program-level
configuration: initial readable misa only when BTYPE is present, value unrestricted.
Actual history derives every local read; CSR-free ordinary/empty scopes remain.
[Common fetched execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
derives branch parity/operand bounds/stateful replay internally. [Independent mixed
source tests](../../../../Tests/NativeReducedSupportedBranches.lean) construct all slots
of a three-word branch/arithmetic public image plus padding; physical ROM/export
and full nonempty native accepted witnesses remain separate.
