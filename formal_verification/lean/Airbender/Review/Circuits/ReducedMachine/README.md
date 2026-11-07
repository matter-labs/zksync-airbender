# Native v2 reduced machine

The active target is [NativeArtifact](NativeArtifact.lean), regenerated from the
unchanged pinned Rust. Start with its [full fixed pool](Tables/Native.lean) and
[short local theorem](Theorems.lean). Both actual sign/high-byte queries follow
from original Clean acceptance. Instruction and execution soundness remain open.
The historical intake below stays separate.

[The historical artifact](Artifact.lean) imports the pinned combined v2 JSON, with 119 equations,
eight scalar and eight timestamp lookups and six tagged lookup queries. Two tags
are native sign/high-byte ID 16; four are original witness expressions. All four
fields use the same explicit fixed setup table, following the current v3 unified
importer pattern with v2 width and coefficients. No disabled row or extra gating
is inserted. Complete source bytes and validated state/decoder/direct memory,
initialization/teardown and delegation-request coordinates are retained. The
existing shift/CSR request keeps its separate coordinates and absent ABI group;
unsupported profiles and invented ABI columns reject.

[Structural checks](../../../Proofs/ReducedMachine/ArtifactChecks.lean) live under
Proofs; [intake controls](../../../../Tests/ReducedMachineImport.lean) and
[emission controls](../../../../Tests/ReducedMachineEmission.lean) retain the
supported and rejected profiles. The complete intake checkpoint passed its bounded gates; the separate fixed-region
addition passed targeted modules/importer/exporter checks and the complete axiom
and public Review audits.

[The native sign/high-byte certificate](Tables/SignHigh.lean) checks all 65,536
literal rows of the registered ID-16 region at the actual reduced offset 196609.
[Its calculations](../../../Proofs/ReducedMachine/SignHigh.lean) stay under Proofs;
[semantic regressions](../../../../Tests/ReducedSignHigh.lean) cover byte/sign
boundaries and altered key/sign/high-byte/tag rejection. The
[strict literal importer](../../../Import/ReducedSetup.lean) validates geometry
and canonical encoding, while the kernel proves contents; parsing alone makes
no semantic assertion. [Importer controls](../../../../Tests/ReducedSignHighImport.lean)
retain that distinction. The FV-only exporter calls the unchanged registered
native table generator. No production circuit code is changed.

This historical intake supplies no execution theorem. Universal public ROM/CSR
binding, decoder membership, initialized combined history,
worker/caller accounting, physical arguments and terminal/padding boundaries
remain open. Stage-two source descriptors are opaque. Table input alone supplies
no setup correctness and cannot close a native-machine claim.
See the [current adaptation map](../../../../V3_ADAPTATION.md) and
[active plan](../../../../FORMAL_VERIFICATION_PLAN.md).

[NativeArtifact](NativeArtifact.lean) is separately regenerated from unchanged
pinned Rust and has 117 equations, 142 variables and fourteen native fixed
regions. The historical artifact has 119 equations, 141 variables and thirteen
regions. Their constraints and coverage are not assumed interchangeable.

[The full native pool](Tables/Native.lean) imports every actual tagged row and
explicit public image/CSR input of the retained fixture.
[Region/tag calculations](../../../Proofs/ReducedMachine/NativePool.lean) recover
exact sign/high-byte membership. [The short row theorem](Theorems.lean) derives
both actual constant queries from original Clean acceptance.
[Mechanical native checks](../../../Proofs/ReducedMachine/NativeArtifactChecks.lean)
retain every query and changed init/request coordinate.
[Pool regressions](../../../../Tests/NativeReducedPool.lean) and
[native/historical intake controls](../../../../Tests/NativeReducedImport.lean)
keep scope and configuration separation explicit. The
[scoped native gate](../../../../scripts/check_native_setup.py) reproduces the
compiler artifact and all fourteen regions, including changed/empty public
inputs and UNIMP padding. No production circuit code is changed.

The active claim is specific to its retained public fixed fixture. Other operation
semantics, universal public/physical setup, full decoding/history and execution
remain open. Current v3 source material does not close those v2 obligations.

The same [row theorem surface](Theorems.lean) now derives all four dynamic selector
domains from accepted native queries and the complete pool. The actual fourth
expressions remain unchanged; no row selector values are supplied. The
[absent-tag regression](../../../../Tests/NativeReducedPool.lean) rejects ID 32.
Domains do not yet identify the operation-selected tag or prove its arithmetic,
memory or CSR effect.

[Selected shift routing](Theorems.lean) now covers all six native shift-mask
cases. The [row model](Row.lean) retains the decoded-mask input and actual
observables. [Mask recovery](../../../Proofs/ReducedMachine/NativeSelectors.lean)
derives all eighteen bit bounds and the operation flags; the
[routing proof](../../../Proofs/ReducedMachine/NativeShiftRouting.lean) derives
all four tags, source-two routing and exact five-bit truncation. The
[truncation certificate](../../../Proofs/ReducedMachine/NativeTruncation.lean)
checks the actual reduced literal columns against the unchanged certified row
lemma, with distinct offsets and no equivalence premise.
[Boundary/rejection checks](../../../../Tests/NativeReducedShift.lean) include
wrong/oversized/unused fields and the distinct standalone sign-fill selector.
Public decoding still needs to supply the packed mask; initialized operands,
numerical shift/PC results and original execution remain open. The later native
port connection below derives actual contribution writes and PC selection.

[Native sign-fill results](Theorems.lean) now derive the actual filler word and
both limb bounds from the same six decoded-mask cases. All three
[minor bits](../../../Proofs/ReducedMachine/NativeShiftMinor.lean), high-limb sign,
truncated amount and fourth query are recovered. The
[128-row literal certificate](../../../Proofs/ReducedMachine/NativeSignFill.lean)
checks the native ID-20 region; [reference definitions](Tables/Shift.lean) retain
logical/positive/zero-shift behavior. [Proof assembly](../../../Proofs/ReducedMachine/NativeShiftFill.lean)
stays separate from the short Review statement.
[Eleven regressions](../../../../Tests/NativeReducedSignFill.lean) include native
shift 0/16/17/31 boundaries and altered filler rejection. Table-37 arithmetic,
full numerical results, public decoding and execution remain open. The direct
large column comparison exceeded existing resource caps and is excluded from
coverage; further work must use a smaller proof evaluation strategy.

[Native contribution and write claims](Theorems.lean) recover both actual table-37
keys/output fields, cross-limb selection, destination address and masked port write.
The outgoing PC is selected from the native default candidate; numerical successor
meaning is separate. [Actual port observables](ShiftWrite.lean) stay small;
[metadata](../../../Proofs/ReducedMachine/NativePorts.lean),
[query recovery](../../../Proofs/ReducedMachine/NativeShiftQueries.lean) and
[write assembly](../../../Proofs/ReducedMachine/NativeShiftWrite.lean) stay under
Proofs. [Eight conditional regressions](../../../../Tests/NativeReducedWrite.lean)
retain discarded lookup participation, asymmetric cross-limb contributions,
zero-shift arithmetic filler and rejected PC mismatches. They do not assert a
complete accepted witness. The decoded mask, architectural rd/x0 binding,
initialized reads, table-37 arithmetic, numeric PC+4/wraparound and original Sail
execution remain separate obligations. No new premise or circuit change bypasses them.

[Complete output-column transport](../../../Proofs/ReducedMachine/NativeShiftColumns.lean)
now covers every native ID-37 row index. Twenty small periodic-block certificates
and bounded block congruence identify the exact earlier certified column getters,
retaining swapped right outputs and the native merged zero/ascending boundary.
[Symbolic boundary reasoning](../../../Proofs/ReducedMachine/ShiftBlocks.lean)
adds no table premise. This closes the literal-column identity gap; canonical
pooled numerical row/query composition and complete results remain separate.
The combined second-output draft still exceeds the unchanged Lean allocation cap
and is excluded from source/coverage. The public row surface and native inputs
are unchanged. Decoder/source/PC/execution and protocol obligations remain open.

[Actual numerical rows](../../../Proofs/ReducedMachine/NativeShiftRows.lean) and
[full-pool numerical queries](Tables/ShiftTheorems.lean) now close the composition
gap above. Every tag-37 row has its exact key and arithmetic outputs; accepted
full-pool queries derive both 16-bit output bounds. Separate low/high getter
proofs and generic vector projections resolve the allocation failure without
changing limits, literals or native circuits. The [selected-row theorem](Theorems.lean)
now fixes both fields and bounds of each [actual contribution](ShiftContributions.lean)
at the canonical value of its actual field-packed key.
[Eleven regressions](../../../../Tests/NativeReducedNumerics.lean) retain real pool
boundary membership, output-order/carry/key rejection and discarded-write
bounds. They are not full accepted execution fixtures. Canonical architectural
source-key binding, original decoding/mask and rd/x0, initialized reads, complete
word results, numerical PC+4/wraparound and execution/protocol boundaries remain
open. No source-range, result or equivalence premise is added.

[Actual initialized clocks and logical memory history](../../Trace/Families/ReducedMachine/History.lean)
now connect this regenerated artifact's ports and clock equations to public
seed construction and accepted native matching. Newest reads and four-tick
terminal row accounting follow without supplied local clocks/order or expected
reads. Word-range preservation, source-key binding, decoding and original
execution remain separate obligations; memory consistency alone is not a
source-bound theorem. See the [native trace guide](../../Trace/Families/ReducedMachine/README.md).

[Original public shift decoding](Decoder.lean) now projects six original RV32
forms to native reduced masks, indices, x0 flags and encoded immediates. The
[short trace claim](../../Trace/Families/ReducedMachine/Decoder.lean) recovers
these from actual query membership and original public byte/stateful Sail
construction; native equations exclude holes/tail. No old split-family decoder
table is transferred. Native Rust preprocessing exports/fixed-ROM fidelity,
other profiles, native write preservation, initialized word ranges and execution
remain separate. [Regressions](../../../../Tests/NativeReducedDecoder.lean)
retain twelve ordinary/x0 forms, original public slots, unsupported amounts,
padding and corrupted-zero-flag rejection.

[Initialized native word ranges](../../Trace/Families/ReducedMachine/Values.lean)
and [both canonical source keys](../../Trace/Families/ReducedMachine/Sources.lean)
now discharge the earlier source-bound gap for selected original shifts. Actual
candidate/filler/query equations and symbolic disjoint-half bounds prove masked
write preservation; unchanged time induction derives the formerly unchecked low
source limb from public seeds and matching. [Concrete setup selection](../../Trace/Families/ReducedMachine/FixedData.lean)
uses the actual pool without table equivalence. Full RV32 word/Sail cell/GPR
execution, numerical PC, other profiles and protocol/physical boundaries remain open.

## Complete RV32 shift words

[References and actual word observables](ShiftResult.lean) retain native source,
selected operand, candidate and write mappings. The [initialized public claim](../../Trace/Families/ReducedMachine/Results.lean)
derives canonical RV32 candidates and original-rd/x0 actual writes without a
public range/result premise. [Pure assembly](../../../Proofs/ReducedMachine/NativeShiftAssembly.lean)
reuses only unchanged arithmetic lemmas after the native numerical connection;
[actual lifting](../../../Proofs/ReducedMachine/NativeShiftResult.lean) uses the
regenerated candidate/write equations. [Eight regressions](../../../../Tests/NativeReducedResults.lean)
retain all shift/sign/count boundaries and discarded candidates. This is not
original Sail cell/GPR transport, PC/instruction execution or a full positive
117-equation fixture. Other combined profiles and setup/physical/protocol
boundaries remain separate.

## Original Sail register states

[Actual native port bindings](../../../Proofs/ReducedMachine/NativeShiftPorts.lean)
now derive mixed source-two register space and low/high rs2 address fields from
native equations, and bind all three decoded indices. Both sources are readonly
refreshes. [The initialized register-history claim](../../Trace/Families/ReducedMachine/Registers.lean)
constructs original Sail GPR/cell states, pre-state reads/actual masked writes,
code/misa frames, decoder replay and final matching. No per-row state/read/result
answer is supplied. [Eight regressions](../../../../Tests/NativeReducedRegisters.lean)
retain aliases/x0 and reject malformed mixed-port fields. The positive port-group
fixture is scoped below complete native 117-equation acceptance. Original operand/
clause execution, numerical PC, other profiles and physical/protocol boundaries
remain separate.

## Original selected operands and clauses

[Operand observables](ShiftOperand.lean) keep actual readonly rs2 participation
separate from the selected register/immediate word. [Native binding](../../../Proofs/ReducedMachine/NativeShiftOperand.lean)
derives the exact form/mask/routing and canonical original immediate fields.
[The initialized clause claim](../../Trace/Families/ReducedMachine/Clauses.lean)
combines those facts with the checked native result and original GPR histories
to execute retained original Sail clauses at the same after-state, including x0.
[Eight regression roots](../../../../Tests/NativeReducedClauses.lean) include all
twelve original Sail forms; positive local execution is not complete native
117-equation acceptance. Numerical PC/preparation/retirement/fetched execution,
other profiles and physical/protocol boundaries remain separate.

## Numerical PC advancement

[Actual PC observables](PC.lean) retain native0/1 and13/14 columns.
[The numerical proof](../../../Proofs/ReducedMachine/NativePC.lean) connects actual
Boolean18/19 and carry/inverse/select34..39 equations to default49/50 and then the
checked final-PC selection. [The public trace claim](../../Trace/Families/ReducedMachine/PC.lean)
derives incoming range/alignment from original public decoding and outgoing bounds
and RV32 PC+4/wrap from native acceptance. No per-row PC/range/carry/successor answer
is supplied. [Eight regressions](../../../../Tests/NativeReducedPC.lean) include
positive actual eight-equation PC slices, explicitly below full native acceptance.
Normal preparation/retirement/fetched execution, other profiles and native
setup/physical/protocol/padding/terminal/init stay separate.

## Original initialized selected-shift execution

[The public retired-history claim](../../Trace/Families/ReducedMachine/Execution.lean)
and [finite fetched-execution claim](../../Trace/Families/ReducedMachine/FetchedExecution.lean)
now derive original successful normal four-byte Sail steps from actual native
matching and public initialization/full stateful shift decoding. [Local proof](../../../Proofs/ReducedMachine/NativeShiftExecution.lean)
uses actual port/GPR/clause and PC facts; [trace composition](../../../Proofs/Trace/Families/ReducedMachine/Composition.lean)
derives row order, all states, decoder replay and terminal PC/cell reads. No local
range/result/state/successor answer is supplied. [Retirement regressions](../../../../Tests/NativeReducedExecution.lean)
and [empty actual-native boundaries](../../../../Tests/NativeReducedFetched.lean)
keep positive local Sail/zero-row scope below complete nonempty117-equation native
acceptance. Other combined profiles and native setup/physical/protocol/terminal/init
remain open; this is selected-profile coverage, not full machine/parity.

## Complete positive native rows

[Ordinary/x0 SLL witnesses](../../../../Tests/NativeReducedWitness.lean) now check
all117actual equations and22lookups at the complete native fixed pool. [Public
nonempty trace construction](../../../../Tests/NativeReducedFixture.lean) proves
activity,state/memory matching,original seed/PC reads and full original sparse/
stateful decoder membership. [Initialized positive execution](../../../../Tests/NativeReducedPositive.lean)
derives actual terminal PC/GPR reads,retains nonzero discarded candidate2 and
rejects an altered actual write. These2SLL examples do not generalize fixtures to
other combined operations or certify native public/setup/physical/protocol spans.

## Other combined arithmetic profiles

[Arithmetic routing/writes](ArithmeticTheorems.lean) derive actual ADD/ADDI/SUB/
LUI/AUIPC candidate assembly,masked destination,address,readonly rs2,zero tags and
default-PC selection under [five explicit native masks](Arithmetic.lean).
[Selector calculations](../../../Proofs/ReducedMachine/NativeArithmeticSelectors.lean)
and [field equations](../../../Proofs/ReducedMachine/NativeArithmeticFields.lean)
stay under Proofs. [Numerical references](ArithmeticResult.lean) and
[internal bounded-input proofs](../../../Proofs/ReducedMachine/NativeArithmeticResult.lean)
retain RV32 wrap/borrow and LUI high words after actual scalar/carry extraction.
Original public arithmetic decoding,initialized ranges/GPR history and execution
remain pending; internal input bounds are not exposed as public answers.
[Nine conditional regressions](../../../../Tests/NativeReducedArithmetic.lean)
are not complete positive accepted arithmetic fixtures. No native fix,defect,
new issue assumption or full-machine/parity claim is introduced.

## Original decoded arithmetic and initialized values

[The arithmetic reference projection](ArithmeticDecoder.lean) now retains original
ADD/ADDI/SUB/LUI/AUIPC and x0 forms, sign extension and raw U-type funct3. [Public
trace decoding](../../Trace/Families/ReducedMachine/ArithmeticDecoder.lean) derives
all actual native fields and excludes holes/tail from accepted mask equations.
[Initialized ranges](../../Trace/Families/ReducedMachine/ArithmeticValues.lean)
and [complete numerical values](../../Trace/Families/ReducedMachine/ArithmeticResults.lean)
discharge all internal input ranges from original public seeds/decoding and native
matching. Scalar checks and decoded immediates prove actual write preservation.
[Decoder/source](../../../../Tests/NativeReducedArithmeticDecoder.lean) and
[range/x0 regressions](../../../../Tests/NativeReducedArithmeticValues.lean) retain
their conditional scope below complete arithmetic execution fixtures. Original
pre-row GPR/cell history, retained Sail clauses/retirement and mixed-profile
fetched execution remain separate, as does native/physical setup fidelity.

## Original arithmetic register histories

[Actual native port proofs](../../../Proofs/ReducedMachine/NativeArithmeticPorts.lean)
now bind rs1/readonly rs2/rd to original register cells under recovered arithmetic
masks. [The public history claim](../../Trace/Families/ReducedMachine/ArithmeticRegisters.lean)
derives all original GPR states, same-pre-state source/old-destination reads,
masked writes, code/misa preservation and original decoder replay. [Eight checks](../../../../Tests/NativeReducedArithmeticRegisters.lean)
retain aliases, x0 and malformed mixed-port rejection. Selected original operand/
clause execution and PC preparation/retirement remain next; AUIPC needs its actual
incoming architectural PC in the constructed row state. No full arithmetic
execution/physical setup/parity follows from register history alone.

## Original arithmetic execution

[Actual selected operand](../../../Proofs/ReducedMachine/NativeArithmeticOperand.lean),
[retained clauses](../../../Proofs/ReducedMachine/NativeArithmeticClause.lean),
[native PC](../../../Proofs/ReducedMachine/NativeArithmeticPC.lean) and
[normal execution](../../../Proofs/ReducedMachine/NativeArithmeticExecution.lean)
now connect the five arithmetic profiles to original Sail preparation/retirement.
AUIPC reads actual incoming native PC after internal control-state transport.
[Public initialized fetched execution](../../Trace/Families/ReducedMachine/ArithmeticFetchedExecution.lean)
discharges both source ranges and all state/PC/decoder replay inputs.
[Regressions](../../../../Tests/NativeReducedArithmeticExecution.lean) retain x0,
nonzero-PC AUIPC, sign/upper immediates and RV32 wrap. Generic modeled setup stays
explicit; mixed shifts still require exact fixed-pool acceptance. Other profiles,
positive nonempty arithmetic fixtures and physical/protocol boundaries remain open.

## Mixed selected shift/arithmetic rows

[The common original projection](SupportedDecoder.lean) changes only the registry
tag of the checked per-profile data; original opcodes/x0/sign/SRAI/raw funct3 are
retained. [Profile/query proofs](../../../Proofs/ReducedMachine/NativeSupportedDecoder.lean)
and [actual local rules](../../../Proofs/ReducedMachine/NativeSupportedLocal.lean)
derive common preservation/register-space/PC/execution. [Initialized fetched execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now composes mixed supported rows using exact fixedData acceptance and derived
common ranges/history/decoder replay. [Public image checks](../../../../Tests/NativeReducedSupportedDecoder.lean)
retain original SLL atPC0 and ADD atPC96 together. Other ordinary operations,
nonempty arithmetic/mixed native fixtures and broader setup/protocol boundaries remain open.

## Actual native bitwise byte and word meanings

[Native bitwise masks/bytes](Bitwise.lean) use actual33/35, with every18flag
[derived](../../../Proofs/ReducedMachine/NativeBitwiseSelectors.lean). [Actual field proofs](../../../Proofs/ReducedMachine/NativeBitwiseFields.lean)
recover all four query triples, inverse256source decomposition, candidate assembly,
readonly addressing, field-masked port and default-PC selection. [Full-pool byte semantics](Tables/NativeBitwiseTheorems.lean)
follow only after kernel-checked actual literal identities. [Two short row roots](BitwiseTheorems.lean)
derive fullRV32candidate/source/selected-operand bounds and bitwise results without
range/result answers. [Tests](../../../../Tests/NativeReducedBitwise.lean) retain
actual byte-row offsets, corruption/domain rejection, x0 participation and sign-bit
values. Explicit mask/tag remain local; original public bitwise decoding, rd/x0/GPR/
operand and Sail execution are next. Common initialized execution is not yet extended.

## Original native bitwise execution connection

[Original decoder fields](BitwiseDecoder.lean) retain XOR/OR/AND and immediate forms,
x0/raw operands/sign extension and actual33/35mask/4/6/7tags. [Actual ports](../../../Proofs/ReducedMachine/NativeBitwisePorts.lean),
[selected operands](../../../Proofs/ReducedMachine/NativeBitwiseOperand.lean),
[original clauses](../../../Proofs/ReducedMachine/NativeBitwiseClause.lean) and
[normal execution](../../../Proofs/ReducedMachine/NativeBitwiseExecution.lean) now
connect accepted native byte results to original Sail states and actual PC+4/wrap.
[Common initialized fetched execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
includes bitwise rows through proved common preservation/history, without public
source/read/result/state/PC answers. New local Sail tests do not certify complete
positive nonempty bitwise native witnesses or native physical/public setup fidelity.

## Actual native comparison numerics

[Comparison model](Comparison.lean) and [effects](ComparisonTheorems.lean) retain
native65/67masks, actual readonly routing, subtraction/borrow, Boolean candidate,
masked port/address and no-jump PC selection. [Full-pool resolver](Tables/NativeConditionalTheorems.lean)
checks all128tag22rows; packed-key/separate-output and inconsistent-flag behavior
differ from split tag43. [Original public projection](ComparisonDecoder.lean)
binds SLT/SLTU/SLTI/SLTIU/x0/sign extension. [Initialized numerical results](../../Trace/Families/ReducedMachine/ComparisonResults.lean)
discharge both operand bounds from native history. Original Sail GPR/clause/PC/
fetched execution and common supported comparison integration remain next.

## Original comparisons in common execution

[Actual comparison ports](../../../Proofs/ReducedMachine/NativeComparisonPorts.lean)
bind original GPR reads/write before shared history transport. [Retained clauses](../../../Proofs/ReducedMachine/NativeComparisonClause.lean)
use checked original signed/unsigned primitives and native numerical results.
[Normal execution](../../../Proofs/ReducedMachine/NativeComparisonExecution.lean)
derives actual bounded PC+4/full wrap and original preparation/retirement.
[Common fetched execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now includes comparisons; both internal read bounds and all states/order/replay
follow from public initialization, full original decoding and exact fixedData
acceptance. This supersedes the preceding numerical-only comparison snapshot.
[Tests](../../../../Tests/NativeReducedComparisonExecution.lean) are original Sail/
conditional native checks, not new full nonempty117-equation native witnesses.
Other ordinary operations and native public/physical/protocol boundaries remain open.

## Native branch routing foundation

[Local branch routing](BranchTheorems.lean) derives actual mask70 selector bits,
readonly rs2/register-space, the present x0 zero-write third port, conditional
lookup fields and target/default PC field selection. [Shared equality-flag proof](../../../Proofs/ReducedMachine/NativeConditionalEquality.lean)
uses actual zero-test polynomials/scalar bounds, without source bounds or zero
answers. Original branch condition/target/public decoding/GPR/Sail execution and
common support remain open. [Tests](../../../../Tests/NativeReducedBranchRouting.lean)
include only five-assertion positive slices, not full native branch acceptance.

## Branch numerical connection

[Actual branch conditions](../../../Proofs/ReducedMachine/NativeBranchCondition.lean)
now derive all six equality/signed/unsigned outcomes from native constraints and
the packed resolver. [Complete actual cleanup semantics](Tables/NativeBranchTheorems.lean)
and [native numerical PC effects](../../../Proofs/ReducedMachine/NativeBranchPC.lean)
derive target/final bounds, RV32 wrap, taken-only bit1 exclusion and conditional
successor alignment. Source/PC/offset bounds, initial alignment and offset parity
remain internal until original public decoding/history discharges them. [Tests](../../../../Tests/NativeReducedBranchResults.lean)
include four-assertion target slices, not complete native accepted branches or
original Sail execution. Common support still excludes branches.

## Original initialized branch numerical connection

[Original BTYPE projection](BranchDecoder.lean) retains raw operands/x0/offset/sign
extension and actual70mask/dummy-rd/raw funct3. [Public numerical result](../../Trace/Families/ReducedMachine/BranchResults.lean)
derives all local ranges/PC/offset/alignment/parity internally from native initialized
history and full original decoding, then actual condition/target/final PC effects.
[Observables](BranchResult.lean) concern native numerical words; original Sail GPR/
clause/fetched execution and mixed branch support remain next. [Source tests](../../../../Tests/NativeReducedBranchDecoder.lean)
are not full nonempty117-equation accepted branches or physical setup certificates.

## Original branch execution connection

[Actual branch port proofs](../../../Proofs/ReducedMachine/NativeBranchPorts.lean)
bind both original sources and present x0 dummy old-read/zero-write before shared
Sail history. [Local retained BTYPE execution](../../../Proofs/ReducedMachine/NativeBranchExecution.lean)
uses actual native condition/PC effects after derived incoming-PC preparation.
[Public fetched execution](../../Trace/Families/ReducedMachine/BranchFetchedExecution.lean)
discharges every source/range/alignment/parity/state/read obligation internally.
Initial public misa readability is explicit, value unrestricted; local CSR reads
follow from history. [Tests](../../../../Tests/NativeReducedBranchExecution.lean)
cover all six original clauses/PC wrap/untaken halfword/taken negative offsets,
not complete positive nonempty117-equation native branches. Common mixed branch
integration and public/physical/protocol/terminal/init/completeness stay separate.

## Mixed branch support

[The common original projection](SupportedDecoder.lean) now includes all six BTYPE
branches. [Actual profile/PC/local rules](../../../Proofs/ReducedMachine/NativeSupportedLocal.lean)
connect branch preservation/addresses/x0 and derived source ranges/parity to its
checked original execution. Incoming PC inputs and operation-specific final bounds
replace universal common PC+4; ordinary proofs remain unchanged. [Public mixed execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
requires initial readable misa only when the public program contains a branch,
value unrestricted and local reads derived through history. [Source/configuration tests](../../../../Tests/NativeReducedSupportedBranches.lean)
are not full positive nonempty117-equation native mixed witnesses. Other combined/
physical/protocol/terminal/init/completeness boundaries stay open.

## Actual native jump local connection

[Jump references](Jump.lean), [all18selector bits](../../../Proofs/ReducedMachine/NativeJumpSelectors.lean)
and [exact native fields](../../../Proofs/ReducedMachine/NativeJumpFields.lean) now
derive masks257/33025, immediate/readonly routing, PC/rs1 base, shared addition,
actual cleanup query, default return/masked rd and final-PC selection.
[Local roots](JumpTheorems.lean) derive output bounds/alignment/raw bit1 rejection
using the certified actual cleanup region, without source-range answers or table
identity. Internal addition input bounds still need original initialization.
[Tests](../../../../Tests/NativeReducedJump.lean) include partial six-assertion
positives, not complete accepted jumps. Original public decoding/GPR/PC/Sail and
common jump execution are open; current supported projection excludes jumps.

## Original initialized jump numerical connection

[Original jump projection](JumpDecoder.lean) now derives native33025/257masks,
raw operands/rd-x0/sign extension/JALfunct3 through full original public membership.
[Return preservation](../../../Proofs/ReducedMachine/NativeJumpReturn.lean) uses
public PC bounds/alignment before initialized range induction. [Public numerical
results](../../Trace/Families/ReducedMachine/JumpResults.lean) discharge raw input
ranges/parity internally and derive canonical return/write/target, wrap and JALR
bit0 cleanup. [Regressions](../../../../Tests/NativeReducedJumpDecoder.lean) are
source/conditional initialized checks, not full native accepted jumps. Original
GPR/retained clauses/fetched execution and common jump support remain next.

[Actual original jump GPR history](../../Trace/Families/ReducedMachine/JumpRegisters.lean)
now follows fresh native source/destination address bindings for all3ports. JAL's
x0 reads remain despite PC base; JALR aliases/old destination/discarded writes remain
in one pre-state. All states/order/final matching/code/misa/decoder replay derive
from initialization/native matching/full original decoding. No CSR-read premise
is needed for GPR history; incoming PC preparation/retained clauses/fetched/common
execution remain separate. [Tests](../../../../Tests/NativeReducedJumpRegisters.lean)
include unchanged group mechanics, not full accepted native jump witnesses.

[Retained jump-clause assembly](../../../Proofs/ReducedMachine/NativeJumpExecution.lean)
now derives original normal retirement from actual native numerical/port bindings and
prepared incoming PC. Its source/alignment/local CSR configuration obligations remain
internal for initialized trace composition; public fetched/common jump support remains open.

[Initialized original jump fetched execution](../../Trace/Families/ReducedMachine/JumpFetchedExecution.lean)
now discharges every local source/alignment/CSR obligation through original public
membership and actual history. It derives original replay/PC chain/terminal observations.
Initial CSR configuration is conditional on nonempty/JALR public program; no local
read/value/state answer is supplied. Common jump integration and full positive native
jump witnesses remain separate.

[Common initialized execution](../../Trace/Families/ReducedMachine/SupportedExecution.lean)
now includes original JAL/JALR across all six supported profiles. PC/byte/query identities
are derived before per-profile native use. Original public incoming alignment feeds
jump return preservation before common range induction; no source-range cycle or
local expected value/state/PC is public. Conditional initial CSR configuration preserves
ordinary/empty and branch-only scopes. [Mixed regressions](../../../../Tests/NativeReducedSupportedJumps.lean)
are public source/configuration evidence, not complete positive native mixed witnesses.

[Word-only memory access](WordMemoryTheorems.lean) now checks explicit LW1025/SW16386,
all18flags, exact port spaces, load shadow/ROM-RAM candidate/masked destination and
unmasked store memory address/write. [Complete actual tables](Tables/WordMemoryTheorems.lean)
certify every offset/separator/ROM row and full padding tail. [Native address roots](WordMemoryAddressTheorems.lean)
derive aligned bounded loads/ROM shadow and RAM-only aligned stores without supplied
source/address bounds. Internal RV32 addition still needs initialized source/decoded
immediate bounds. Original values/initialized memory/code frames/
Sail/common integration stay open; memory ports are not all GPR events. The fixed8word
ROM is not an arbitrary original public image. Positive address slices are not full
accepted117-equation native LW/SW witnesses.

[Original LW/SW decoding](WordMemoryDecoder.lean) and its
[public root](../../Trace/Families/ReducedMachine/WordMemoryDecoder.lean) now bind
allten actual native query fields from original byte/stateful sparse/padded
membership, retaining x0/sign extension and native unused indices. Holes/tail are
excluded by accepted packing. Original initialized memory/preservation/code frames/
Sail/common execution still remain open; logical decoder image is not the native ROM.

[Initialized LW/SW numerical results](../../Trace/Families/ReducedMachine/WordMemoryResults.lean)
now derive fresh ALL3mixed-port cells, effective addresses/ROM-RAM or unmasked store
writes and PC+4/wrap, with every source/read/range answer discharged by public
initialization and proved write preservation. [Native port nonoverlap](../../../Proofs/ReducedMachine/NativeWordMemoryPorts.lean)
excludes SW from ROM-prefix WORD CELLS. Original independent shadow/ROM-byte input
construction, memory-aware states/code-byte frames/Sail/common execution remain open.

[Independent public shadow seeds](../../Helpers/Memory/ReducedMachineShadowImage.lean)
now have derived architectural projection/uniqueness/clocks/ranges and
[actual numerical results](../../Trace/Families/ReducedMachine/WordMemoryShadowResults.lean).
The fixed ROM/original byte-image, projected row states/code-byte frames and retained
Sail/common execution remain separate; every ignored shadow token stays in matching.

[Exact native ROM bytes](../../Trace/Families/ReducedMachine/ROMImage.lean) now come
from an explicit original Sail byte constructor for the actual8wordfixture/full
UNIMP tail. Full public extraction/every aligned read and outside/register frames
are derived, without arbitrary image/table identity. [Native LW ROM read](WordMemoryROMTheorems.lean)
connects actual accepted address/ROMoutput to those constructed bytes; ignored
shadow values stay independent. Projected chronological memory/Sail states,
byte-code frames/retained clauses/common memory execution and physical fidelity
remain open. [Nine tests](../../../../Tests/NativeReducedROMImage.lean) are not full
positive accepted native memory witnesses.
