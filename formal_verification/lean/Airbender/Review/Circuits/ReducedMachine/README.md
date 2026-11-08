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

[Actual word-memory domains](../../../Proofs/ReducedMachine/NativeWordMemoryDomains.lean)
and [projected initialized history](../../Trace/Families/ReducedMachine/WordMemoryHistory.lean)
now retain full native shadow matching while deriving chronological architectural
Sail states/code-byte frames/stateful replay. Only ROM-prefix LW shadow Sail
transfers are filtered; SW memory OLDREAD/write remains. Original same-pre-state
GPR/RAM effects/retained clauses/common memory execution remain next. [Ten tests](../../../../Tests/NativeReducedWordMemoryHistory.lean)
are not full positive nonempty accepted native LW/SW.

[Original same-pre-state LW/SW transfers](../../Trace/Families/ReducedMachine/WordMemoryTransfers.lean)
now derive all retained native reads/OLDREADs, original GPR/RAM observations and
final writes. Exact constructed ROM bytes/past frames supply architectural ROM
reads independently of ignored shadow values. Original unmasked load-to-x0 writes
retain their read; SW copies rs2 to actual RAM without dummy-rd masking. Numerical
source/range/address/PC/result obligations are discharged internally. Retained
LOAD/STORE access/privilege/exception clauses and normal/fetched/common memory
execution remain next; [eight regressions](../../../../Tests/NativeReducedWordMemoryTransfers.lean)
are not complete positive nonempty accepted native memory witnesses.

[Retained original LW/SW clauses](../../Trace/Families/ReducedMachine/WordMemoryClauses.lean)
now execute at actual projected row states through original virtual/physical access.
Initial reference configuration and public ordinary RAM-cell domain describe
meaningful inputs; actual ROM bounds/RAM address origins/past history derive every
local address/CSR/permission/success. Empty/transfer-only scopes remain CSR-free.
These inputs are not native/physical enforcement. PC preparation/normal retirement,
fetched/common memory remain next. [Nine regressions](../../../../Tests/NativeReducedWordMemoryClauses.lean)
include positive ORIGINAL LW-to-x0/SW, not full nonempty native memory witnesses.

[Separate original LW/SW normal/fetched execution](../../Trace/Families/ReducedMachine/WordMemoryFetchedExecution.lean)
now derives actual PC preparation/retirement/stateful source replay/native clock
order/PC chain and terminal architectural readers. Actual readonly aliases,
OLDREADs/unmasked x0 loads/SW writes and full shadow matching remain. Existing
initial platform/domain inputs stay explicit; empty programs remain CSR-free.
[Normal](../../../../Tests/NativeReducedWordMemoryRetirement.lean) and [empty fetched](../../../../Tests/NativeReducedWordMemoryFetched.lean)
regressions are not full nonempty native memory witnesses. Common mixed memory
requires fresh projected histories/per-profile frames; no all-events-GPR reuse.

## Common seven-profile projection and native laws

[Unified original projection](UnifiedDecoder.lean) wraps unchanged six-profile
support plus LW/SW. [Exact native profile transport](../../../Proofs/ReducedMachine/NativeUnifiedDecoder.lean)
retains original instructions/PC/bytes and all ten query fields. [Fresh common
local laws](../../../Proofs/ReducedMachine/NativeUnifiedLocal.lean) select actual
write/x0/three-port domains before common initialized induction. SW memory writes
remain unmasked; only LW ROM shadows filter from Sail. This local/history
foundation does not yet prove common mixed retained instruction execution.

## Common original execution connection

[Fresh original dispatch and supported-row filter identity](../../../Proofs/ReducedMachine/NativeUnifiedExecution.lean)
now connect actual selected GPR rows to common projected states; actual selected
memory ports derive initialized address origins before RAM-domain use. [Common fetched execution](../../Trace/Families/ReducedMachine/UnifiedFetchedExecution.lean)
composes checked original normal execution and actual terminal observations.
It retains exact NativeROM memory input scope and all older ordinary public-code
interfaces. Other native operations/protocol/physical boundaries remain open.

## Actual native MOP local arithmetic

[The MOP reference observables](MOP.lean) and [short local theorem](MOPTheorems.lean)
now derive native field ADD/SUB/MUL, canonical result below Mersenne31, readonly
second GPR routing, candidate/rdmask and default-PC selection from actual native
constraints. No source<modulus or desired output/range is assumed. [Fresh field
and borrow proofs](../../../Proofs/ReducedMachine/NativeMOPResult.lean) reuse PURE
lemmas only after actual native bindings. Eleven [regressions](../../../../Tests/NativeReducedMOP.lean)
include three seven-equation positive slices, not complete accepted rows.
Original public MOP decoding/custom reference/initialized/fetched/common execution
and CSR/delegation remain open; existing seven-profile roots stay unchanged.

## Actual native CSR table and local request observables

[The complete special-CSR certificate](Tables/CSRTheorems.lean) checks all4,096
native rows from stored blocks: support1984/1988/1989, delegation1988/1989.
[The local CSR root](CSRTheorems.lean) derives actual query/flags/ports, bounded
oracle, delegation zero, candidate/rdmask/default-PC and imported masked request
fields. The source-high lookup bounds ABI offsets; in-cycle index3 is metadata.
Thirteen [regressions](../../../../Tests/NativeReducedCSR.lean) include positive
full-pool table membership and native six-equation slices, not complete accepted
CSR rows. Original public CSR/custom/nondeterminism/privilege execution and
initialized/common/caller/worker/accounting/protocol boundaries remain open.

## Separate actual runtime CSR region

[The runtime CSR root](Tables/RuntimeCSRTheorems.lean) checks all4,096 native
regional rows for runtime allow-list1984/1991, only1991 delegated. It is separate
from the preserved complete pool's fixture1988/1989 and excludes bigint1994.
The scoped native exporter and strict importer preserve concrete data/source/
configuration boundaries; eight [theorem regressions](../../../../Tests/NativeRuntimeCSR.lean)
and importer controls check the distinction. Full runtime pool/query/trace/worker/
reference/physical connections remain open; no equivalence transfers prior claims.


## Runtime CSR pool and actual selected-query effects

[The complete constructed pool](Tables/RuntimePool.lean) shares all thirteen
non-CSR regions and the retained eight-word ROM, selecting the separately exported
runtime CSR data. [Fresh partition/tag proofs](../../../Proofs/ReducedMachine/NativeRuntimePool.lean)
isolate actual members; [native query projection](../../../Proofs/ReducedMachine/NativeRuntimeQueries.lean)
derives both sign queries/all four dynamic domains on this table. [The local root](RuntimeCSRTheorems.lean)
derives1984/1991 support, only1991 delegation, bounded oracle/zero return and all
imported masked request fields/ABI bound from actual constraints and explicit local
mask. Sixteen [regressions](../../../../Tests/NativeRuntimePool.lean) preserve old
fixture separation and conditional-native scope. Original public CSR source/
initialized execution/request clock/issuance, workers/accounting/protocol and
general runtime public/physical setup remain open; no equivalence transfers old
execution coverage and no parity is inferred.


## Original public CSR decoding

[The CSR projection](CSRDecoder.lean) retains original register CSRRW/raw operands/
x0 and unsigned 12-bit index. [Source/field calculations](../../../Proofs/ReducedMachine/NativeCSRDecoder.lean)
recover every actual native query field from full original public membership;
accepted packing rejects holes/tail. [Short trace roots](../../Trace/Families/ReducedMachine/CSRDecoder.lean)
derive the local mask before runtime CSR effects, preserving all rows/boundaries.
Fourteen [regressions](../../../../Tests/NativeReducedCSRDecoder.lean) retain an
independent original byte image and unsigned fields. Initialized reads/CSR execution,
request clock/issuance, workers/accounting and general native/physical setup remain open.


## Initialized CSR GPR history

[Fresh port laws](../../../Proofs/ReducedMachine/NativeCSRPorts.lean) retain original
rs1/readonly x0/rd and both refreshes/OLDREAD/aliases. [Write preservation](../../../Proofs/ReducedMachine/NativeCSRPreservation.lean)
uses actual oracle bounds and original rd masking before shared range/x0 induction.
[Value roots](../../Trace/Families/ReducedMachine/CSRValues.lean) and [GPR history](../../Trace/Families/ReducedMachine/CSRRegisters.lean)
derive all native ranges, chronological states, original reads/write, byte/misa
frames and decoder replay from public inputs/matching. CSR instruction/delegated
RAM effects, PC retirement, caller issuance/worker accounting and physical setup
remain separate; existing mixed execution scopes are unchanged.


[Original CSR source/request observations](../../Trace/Families/ReducedMachine/CSRRequests.lean)
now bind actual source35/36 to the original same-prestate rs1 word and imported
request ABI-high/kind to its natural high half/original unsigned CSR index, under
full initialized runtime history. Full RV32 words are retained before field cast.
This is not original CSR execution or actual issuance/worker accounting; metadata
index3 and main state/memory matching alone do not establish those connections.


[CSR local caller clocks](../../Trace/Families/ReducedMachine/CSRCallers.lean)
now derive the exact imported (w2+3,w3) tuple, bounded/nonzero slot3 value and
chronological multiplicity-selected projection from accepted initialized history.
All GPR slots precede it; next native clock follows. This is row-local observation;
sequence-HIGH normalization, actual issuance and global worker accounting remain
separate. No v3 F03 conclusion follows from unique local caller clocks.


[Selected-unrolled caller argument normalization](../../Trace/Families/ReducedMachine/CSRArgument.lean)
now binds actual caller origins to reviewed stage2/quotient reference formulas.
The native unrolled constructor passes sequence0; its extra high contribution is
zero. Witness terms scale before gamma/literal additions. Exact key agreement at
unit scaling precedes compression; no injectivity, LDE or worker-ledger claim.

## Main delegation auxiliary and scalar row component

[Typed geometry](AuxiliaryColumns.lean), [Same-read main artifact](AuxiliaryArtifact.lean),
[Caller/component interface](Delegation.lean), [Short roots](DelegationTheorems.lean),
[Kernel bindings/calculations](../../../Proofs/ReducedMachine/NativeCallerDelegation.lean),
[Regressions](../../../../Tests/NativeCallerDelegation.lean),
[Intake controls](../../../../Tests/NativeReducedAuxiliaryImport.lean).

Auxiliary quartic92 is distinct from body logical92. All18 native stage2 fields
and active initialization/state/masking families remain retained. The full domain
checks every ordinary body row and keeps every auxiliary contribution; the active
logical Trace.Accepted interface is not substituted for padding. Native polynomial
sum derivation and the actual claim fold connect full caller and worker row sums.
The denominator keeps the checked selected-constructor sequence0 scope, with no
extra public chunk sequence. No stream/initialized-read/expected-result premise;
no inactive-pole removal, multiset matching, fulfillment/converse/accounting or
physical/global dispatch/capacity/sequence/refinement claim. Full matching and
initialization/history/filtering and original CSR/MOP execution remain open.

[Configured caller/worker composition](ConfiguredDelegationTheorems.lean) now
uses the exact same selected worker outputs for native metadata/capacity checks
and the existing full-row scalar claim fold. Derived Boolean multiplicities give
an exact canonical count below the field modulus; at most2048 selected proofs.
This is a source-reference normalized component, not a whole native verifier or
issued/matched execution. No inactive auxiliary contribution is discarded. Native
matching/initialization and faithful padding/filter/history remain necessary
before active caller/worker streams, bounds or accounting can be established.

[Native public memory-boundary composition](MemoryBoundaryTheorems.lean) now
connects every selected worker's full43-by-1048575 read/write factor products to
the statement's main grand claims and32-register/PC boundary contributions.
[Observables/accepted component](MemoryBoundary.lean) retain x0's timestamp,
full32-bit public value/PC splitting before field cast and native initial PC0/time4.
Successful boundary inverse relations derive their denominator checks; no worker
nonzero/injectivity/cancellation premise. Main grand claims remain full opaque
protocol outputs, not main RAM-only ratios. Main auxiliary/state/mask/init claim
bindings, full token matching/initialization, active ranges/keys and physical
refinement remain open. Fourteen pure/reference/conditional regressions include
a positive helper-only boundary, not a complete native witness or defect.

[Main auxiliary and joint-product roots](MainAuxiliaryTheorems.lean) now bind
actual returned main claims to the full8388607-row source chain: three memory
slots96/100/104, state108, execute masking112, unmasked initialization116 and
adjacent grand120, with actual first/last boundaries. Complete native body and
six initialization-padding polynomials remain; no execute1/Boolean-execute or
desired per-row read/range/clock/result premise. The actual masking polynomial
and all factors remain, with no cancellation. Same-list composition with the
worker/public boundary closes joint product balance at this stronger normalized
interface. Token matching, initialized history/active ranges, initialization
range/sorting/window checks and physical/general refinement remain open.

Original native equation31 additionally derives execute0-or1 and actual N-versus-D
mask selection from full body acceptance, with no Boolean/activity premise.

[The native key/token bridge](MemoryTokenTheorems.lean) now connects the unchanged
original Clean port tokens to all three actual main precompression keys, without
selector/range/activity premises. Field complement converts native register1/RAM0
to Clean space0/1 losslessly; raw limbs, OLDREADs, readonly refreshes and actual
third writes remain. [Observables](MemoryTokens.lean) retain all43 worker keys and
challenge factors. Pure permutation equivalence does not assert native matching,
initialized reads or issuance/accounting. Seventeen regressions include raw/wide
fields, duplicate multiplicity, encoded-image limits and scalar collisions.

[The joint main-argument root](MainArgumentTheorems.lean) now derives existing
scalar/product/capacity conclusions from one shared body/auxiliary observation
record and the same returned worker list. Distinct claims remain distinct; no
active filter, desired stream or matching premise. Rust Option/physical-output
refinement and full token matching/initialization remain separate.

[Complete body witnesses and padding scope](BodyPaddingTheorems.lean) now check
all117 equations/22 lookups for runtime CSR1991/x0 under both execute values.
[The active nonempty fixture](../../../../Tests/NativeCSRPositive.lean) also checks
all native memory aliases, original public decoding/initialization and derived
caller clock7. Execute0 still requests in the BODY but rejects the active logical
trace interface. This is no auxiliary/global/worker attack or native defect;
faithful physical padding/filtering and full matching remain open.

[Decoder access](DecoderArgumentTheorems.lean) now retains actual quartic72 and
all ten original decoder fields on the SAME full-domain main rows/auxiliaries.
[Proof calculations](../../../Proofs/ReducedMachine/NativeDecoderArguments.lean)
derive the execute-weighted relation and active pole exclusion. The complete
CSR body plus this individual relation admits execute0/request1 for every decoder
challenge; [the local certificate](../../../Proofs/ReducedMachine/NativeDecoderPadding.lean)
claims no table-multiplicity/sum/last-row/global/worker/physical acceptance or
native defect. [Regressions](../../../../Tests/NativeDecoderArguments.lean) and
[intake controls](../../../../Tests/NativeDecoderAuxiliaryImport.lean) preserve
that boundary. Global faithful inactive filtering and initialized matching remain open.

[Decoder table sum](DecoderTableTheorems.lean) retains physical witness9 separately
from logical body IDs, physical setup6-through15 and quartic88/72. The actual
zero/last difference-polynomial boundary derives full ordinary auxiliary-sum
and last-value equality; it does not assume either auxiliary last value zero.
[Strict intake controls](../../../../Tests/NativeDecoderTableImport.lean) and
[regressions](../../../../Tests/NativeDecoderTable.lean) preserve scope. Public
physical setup/extraction, inactive request filtering and initialized global
matching remain open; no prior local example becomes a native defect.

[Constructed physical decoder setup](PhysicalDecoderSetupTheorems.lean) retains
the whole public indexed slice and ordinary native tail, then normalizes only the
reserved last row. Original Sail source evidence follows from actual body plus
ordinary-table membership; membership/extraction remains explicit. Acceptance is
checked on constructed setup observations, with no equality transfer from arbitrary
tables or identification with fixed native ROM. [Split controls](../../../../Tests/NativePhysicalDecoderSetup.lean)
retain a small hole fixture and a separate exact-capacity empty-image/tail test.

## Native full-domain logical token boundary

[The native ledger roots](TokenLedgerTheorems.lean) bind all ordinary main/worker/public
tokens to the checked scalar product and retain exact precompression matching as
an explicit logical trust boundary. Identical inactive incoming port/state tokens
cancel only as duplicate-preserving multisets. Initialization/teardown, every worker
access and caller requests remain. [Controls](../../../../Tests/NativeTokenLedger.lean) do not establish
initialized worker history, active ranges/key refinement, fulfillment or physical
cryptographic extraction. Original initialized execution interfaces are unchanged.

## Native active main-state path

[The main-state theorem](MainStateHistoryTheorems.lean) derives actual active main chronology,
clock bounds, four-tick counts and distinct0/1/2 write slots from complete native
body acceptance and the same explicit full token matching. All ordinary main rows
are considered before selecting execute1. Worker/init memory tokens and inactive
caller requests remain in their original ledgers. This is no initialized worker
memory history, CSR/MOP/Sail execution, issuance/accounting or physical extraction
claim. Original initialized execution interfaces are unchanged.

## Native adjacent initialization records

[The initialization ordering roots](InitializationOrderingTheorems.lean) derive repeated adjacent
actual token-address exclusion from native ordering polynomials, complete body
remainder/borrow checks and unmasked padding. Only zero padding can repeat at
adjacent comparison positions; the last two physical rows are excluded. This
supplies no global uniqueness, address range, public seed image, initialized
worker read or physical extraction. Original initialized execution is unchanged.

## Native initialization-address pair oracles

[The same-main pair roots](InitializationRangeTheorems.lean) retain all ordinary native rows and
the existing complete body, auxiliary chain, padding and adjacent ordering.
Separate base4/quartic28 observations yield the source pair equation, including
its duplicate-pole limit. Address ranges and logical lookup extraction are still
open; these local relations do not establish initialized worker reads or change
original execution.

## Complete native scalar16 family

[The same-main scalar16 roots](Scalar16Theorems.lean) derive ordinary auxiliary-sum
equality and reserved-last consistency from the native polynomial divisor.
All four body pairs and the initialization-address pair remain, including every
ordinary row and pole auxiliary. Physical multiplicity/setup observations do not
yet authenticate the public scalar table or extract lookup membership. Address
bounds, combined initialized worker history and accounting remain open.

## Constructed native scalar16 lookup boundary

[The same-main constructed lookup roots](Scalar16LookupTheorems.lean) retain the complete
source component and derive both initialization-address bounds from ALL actual
family queries on the constructed prefix/zero-tail table. The last normalization
value is derived symbolically. Logical lookup membership remains an explicit
cryptographic extraction boundary; no initialized worker history or accounting
is supplied, and original execution is unchanged.

## Natural initialization sorting

[Actual same-main sorting and nonpadding uniqueness](InitializationSortedTheorems.lean) follow from
the existing complete source, derived full-family address ranges, native
subtraction and six padding polynomials. All ordinary rows are included; repeated
padding remains. Public windows/image/seeds and combined worker memory history
are separate obligations; original execution is unchanged.

## Public initialization endpoint binding

[All twelve actual public boundary polynomials](InitializationBoundaryTheorems.lean) bind both six-field
endpoint records and derive the public address interval for every ordinary row.
The normalized last row is excluded. Cross-chunk windows, public image/seeds
and combined initialized worker history remain separate obligations.

## Native initialization windows

[Successful native windows and global nonpadding uniqueness](InitializationWindowTheorems.lean) retain
the actual zero-terminal fallback and all padding records. The fallback derives
a wholly padded previous ordinary chunk. The indexed normalized batch is separate
from full main-ledger/protocol extraction, public seeds and initialized workers.

## Same-main initialization ledger

[Constructed same-main initialization views](InitializationBatchTheorems.lean) retain complete main/
caller/worker arguments and the SAME full logical ledger. Bounds/order/uniqueness,
both-sided unmasked token membership and existing main chronology share one actual
proof list. Public seeds and initialized combined worker memory remain open.

## Actual native seed ledger

[Native seed domains and padding cancellation](InitializationLedgerTheorems.lean) derive canonical
RAM32 zero seeds and exact duplicate-preserving matching equivalences on the same
full ledger. Six-field padding cancellation keeps active ports and every worker
access. Public domain/image/seed coverage and combined worker history remain open.

## Observed native seed domain

[Unique observed seed cells](InitializationSeedDomainTheorems.lean) derive actual seed-address/cell Nodup
and exact canonical zero-token encoding on the SAME native main list. This is an
observed domain; independent public image coverage, alignment, shadow/architectural
separation and combined worker history remain separate.

## Complete native seed boundary

[Complete GPR/RAM seeds and memory matching](InitializationSeedBoundaryTheorems.lean) retain all32 public
registers, x0 timestamps and all43 worker ports, deriving exact shadow partition
and memory-only matching from the SAME full ledger. Actual Sail public-image
reads and initialized combined worker memory remain open.

## Constructed original initial image

[Original Sail reads and complete native memory matching](InitializationPublicImageTheorems.lean) derive
architectural initial-image reads from explicit PC/GPR/RAM inserts, preserving
the exact ROM and separate native shadows. The declared three-byte logical halo
supports unaligned RV32 cell reads. Arbitrary public-state coverage, combined
chronological worker history, keys and accounting remain open.

## Actual native main-memory history

[Actual read sources and main history](NativeMemoryHistoryTheorems.lean) derive read-token provenance
for every selected worker batch, and complete Clean main-memory history when the
batch is explicitly constructed empty. The real accepted trace retains actual
seeds/teardown and all main ports. Nonempty-worker chronology, active read bounds,
keys/accounting and original CSR/MOP/worker Sail execution remain open.

## Actual active-worker clock sources

[The actual worker-clock source theorem](ActiveWorkerClocksTheorems.lean) derives that any unbounded
actual read clock has an exact multiplicity-one worker-write source on the same
complete ledger. Accepted inactive workers have both raw clock limbs zero; all
worker observations remain. Active clock progress/bounds, initialized worker
reads, keys and request accounting remain open.

## Every native request and active main caller clocks

[Request gates and caller clocks](CallerRequestsTheorems.lean) derive request shape on EVERY ordinary
main row and canonical unique clock observations on the EXISTING active main-state
projection. All physical requests/poles remain; inactive-request clocks and actual
worker issuance, fulfillment, initialized history and accounting remain open.
