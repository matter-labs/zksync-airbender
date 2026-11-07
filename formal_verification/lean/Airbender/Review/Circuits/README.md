# Circuit review

## Checked results

| Family | Claim and interfaces |
| --- | --- |
| ADD/SUB/LUI/AUIPC | [Guide](AddSub/README.md), [theorems](AddSub/Theorems.lean), [model](AddSub/Model.lean) |
| Word-memory rows | [Guide](WordMemory/README.md), [theorem](WordMemory/Theorems.lean), [model](WordMemory/Model.lean); complete initialized fetched Sail execution under documented ROM/RAM/platform profiles |
| Jump/branch/SLT fixed effects, public/native exported decoding and PC bounds | [Guide](JumpBranchSlt/README.md), [claims](JumpBranchSlt/Theorems.lean), [observables](JumpBranchSlt/Model.lean); [complete fetched execution](../Trace/Families/JumpBranchSlt/Execution.lean) and terminal matching checked under the stated initial CSR profile |
| Unsigned MUL/DIV numerical results and actual masked writes | [Guide](MulDiv/README.md), [claim](MulDiv/Theorems.lean); all four numerical results and zero divisors checked under explicit local interfaces; public decoding/history/original Sail remain open |
| Subword native lookup import | [Guide](SubwordMemory/README.md), [claim](SubwordMemory/Lookups.lean), [artifact](SubwordMemory/Artifact.lean); native metadata/routing, derived offset/trap controls, canonical load values and actual load/store write assembly; decoded normalization/history/execution open |

The remaining v2 families are tracked in the [plan](../../../FORMAL_VERIFICATION_PLAN.md).
Local row soundness and whole execution are distinct milestones.

[Subword public decoding](SubwordMemory/Decoding.lean) now derives original
LB/LH/LBU/LHU/SB/SH fields and bounded actual load writes from native acceptance
and constructed public logical setup membership. All seven full native fixtures
and five decoder rejections pass. Exported decoder fidelity, decoded-key
normalization, initialized history and original subword execution remain open.

[Subword decoder export fidelity](../Trace/Families/SubwordMemory/NativeDecoder.lean)
now checks every row of the actual thirteen-word native export against original
public Sail setup, including negative immediates, x0, unsupported LW and the
complete sentinel tail. This adds no general compiler refinement or initialized
subword execution claim.

[Native subword history](../Trace/Families/SubwordMemory/History.lean) now
connects all three actual mixed register/RAM ports to complete original Clean
history and newest reads from public Sail initialization and native matching.
Readonly shadows/alias refreshes and actual masked writes remain. Native clock
carry/rejection and eight initialized fixtures pass. Original subword execution,
canonical word/key bounds and architectural ROM projection remain separate.

[Initialized subword payload bounds](../Trace/Families/SubwordMemory/Values.lean)
now derive all native read/write/terminal ranges from actual initialization,
matching and public original decoding. Exact packed fields and disjoint native
byte contributions bound merged stores. Eight complete traces use one public
state for instruction and seed bytes, including shadows, x0 and aliases.
Architectural address/ROM/byte effects and original subword execution remain
separate next dependencies.

[Initialized subword native addresses](../Trace/Families/SubwordMemory/Address.lean)
now derive actual RV32 effective addresses, offsets and containing aligned port
words from public seed reads, original decoding and native matching. Eight full
initialized traces and signed/wrap native boundary certificates pass. The next
connection is original byte/halfword effects and execution, with architectural
ROM projection explicit.

[Initialized subword load values](../Trace/Families/SubwordMemory/Loads.lean)
now derive original Sail extension functions and actual masked writes from
native controls and initialized words. The single native ROM index and retained
alignment are derived; an odd discarded halfword remains in a full initialized
trace. Store byte windows, architectural ROM/access/exception binding and original
subword retirement/execution remain next dependencies.

[Initialized subword store bytes](../Trace/Families/SubwordMemory/Stores.lean)
now connect actual native clearing/placement queries and write muxes to every
changed/preserved SB/SH byte. Actual source/old ranges and selectors are derived;
full literal helper domains remain unchanged. Architectural memory/ROM and
original access/exception/retirement remain separate next dependencies.

## Combined native reduced machine

[The reduced artifact](ReducedMachine/Artifact.lean) retains all native local
row equations/queries, the complete source bytes and validated state, decoder,
initialization and request coordinates. [The guide](ReducedMachine/README.md)
separates that intake from pending native fixed setup, execution and argument
connections. Existing standalone family results do not establish this machine.

The [active regenerated reduced target](ReducedMachine/NativeArtifact.lean)
keeps the historical JSON separate. Its [local shift claim](ReducedMachine/Theorems.lean)
derives selected tags, operand routing and five-bit truncation from native
acceptance plus an explicit decoded packed mask. This is native combined-row
coverage; public decoding, numerical results/PC and execution remain open.

The [native reduced shift claim](ReducedMachine/Theorems.lean) also derives the
actual sign filler from accepted native sign/control/amount queries, including
logical/positive/zero-shift cases. Both actual table-37 queries, native field
assembly, destination address/masked port write and default-PC candidate selection
are also derived. Table-37 arithmetic, full numerical shift/PC results, public
decoding and initialized execution remain separate obligations.

[Both actual reduced shift columns](../../Proofs/ReducedMachine/NativeShiftColumns.lean)
now have complete getter transport to prior certified native columns, including
all periodic values, the merged native boundary and reversed right output order.
The public row surface is unchanged. Canonical pooled numerical row/query
composition, complete shift results and execution remain open; the unverified
second-output assembly draft is excluded after allocation-limit failures.

### Native Blake2 worker

[Worker guide](Blake2Worker/README.md) describes fresh native row intake, actual43-access ABI metadata and checked local control bounds. Worker tables/memory/protocol acceptance and accounting remain separate; no historical acceptance is transferred.

The [native worker fixed-pool roots](Blake2Worker/TablesTheorems.lean) now certify all344384 actual rows and five XOR regions. Actual compiled query/worker memory/protocol composition remains separate.

The [native worker lookup-effects root](Blake2Worker/QueriesTheorems.lean) now connects every208 fixed query and88 range expression to complete local acceptance on the actual worker pool. ABI/memory/processing/round/reference/protocol execution remains separate.

The [native worker ABI-local memory root](Blake2Worker/MemoryTheorems.lean) now derives canonical
pointer alignment/scalar-implied bounds and all43 actual Boolean borrow and
timestamp-difference laws from complete local acceptance. Initialized16bit reads,
raw clocks/processing multiplicity, alltoken matching and issued worker/protocol
accounting remain open. Main histories/frames do not cross unproved worker actions.

The [normalized worker processing root](Blake2Worker/ProcessingTheorems.lean) derives Boolean multiplicity
and allinactive memory-field zeroing under an explicit additional native
individual-convention relation. This relation is separate from the352 local JSON
equations and physical quotient/LDE/last-row enforcement. Worker keys/tokens,
initialized active ranges/clocks, cancellation and issuance/accounting remain open.

The [unused worker memory-key roots](Blake2Worker/MemoryKeysTheorems.lean) retain all43 access/read/write
sides and common processor clock, deriving stage2/quotient-unit reference key
agreement and equal products before division under normalized processing
acceptance. Active initialization/keys, native auxiliaries, full matching and
issuance/accounting remain open; no main frames cross unproved worker actions.

The [worker auxiliary roots](Blake2Worker/AuxiliaryTheorems.lean) now telescope all43 native memory factors
across the selected full domain under an explicit individual normalized auxiliary
acceptance contract and actual first/last public-claim boundaries. Separate typed
quartic slots, no division or terminal claim1. Product balance does not prove
full token matching/initialization or a delegation ledger; active ranges/keys/raw
clocks and issuance/converse/accounting remain open. No main frame crosses an
unproved delegated action, and physical enforcement stays separately scoped.

The [worker delegation sum roots](Blake2Worker/DelegationTheorems.lean) derive ordinary auxiliary sums from
native polynomial divisibility/degree/domain/sample inputs and normalize the
unified statement's returned-claim accumulator component. Main claims remain
opaque until their actual caller auxiliaries are connected; scalar balance is
not issuance/matching/converse/accounting. Physical/global capacity/dispatch/
challenge boundaries and active initialized memory effects remain open.

The [main caller auxiliary roots](ReducedMachine/DelegationTheorems.lean) now derive main claims from all native
ordinary-row auxiliary values and connect them to worker-row scalar sums. Separate
quartic92 and body92 roles remain explicit. Full body acceptance here does not
require every row active; existing initialized logical trace/history roots remain
unchanged. No inactive contribution is discarded, and padding/filter/matching,
global sequence/capacity/dispatch/challenge boundaries and accounting stay open.
