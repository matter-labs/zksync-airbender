# Shared helper review

[Properties](Properties.lean) defines soundness, completeness and the observable
circuit model independently of any decoder/history claim. [Core](Core/README.md)
contains reused word and original Sail definitions; [tables](Tables/README.md)
states the current range-table boundary. [Context](Context/README.md) exposes
clock contracts and native logical matching; [decoder](Decoder/README.md) exposes
the native ten-column query; [memory](Memory/README.md) exposes
port interpretation and initialized history. Their definitions remain independent
of public whole-execution claims.

[Native mul/div arithmetic](../Circuits/MulDiv/README.md) reuses the unchanged
shared [integer byte-column theorem](../../Proofs/Arithmetic/Multiplication.lean).
Its v2 circuit connection derives all byte, carry and output bounds from actual
queries/assertions; the existing word and logical-history definitions are
unchanged. Original Sail execution is still a separate connection for this family.

## Unsigned MUL/DIV helpers

[Stateful public setup](Decoder/StatefulSetup.lean) retains actual extension-configuration reads. [The native context](Context/MulDiv.lean) and [full decoder membership](Decoder/MulDiv.lean) feed the [initialized trace claims](../Trace/Families/MulDiv/README.md).

## Subword native context

[The separate registry](Context/SubwordMemory.lean) selects actual native
subword state, decoder, mixed memory ports and ROM-dependent constraints.
[Native clock laws](../../Proofs/Trace/Families/SubwordMemory/History.lean)
discharge the unchanged shared contract; [public history](../Trace/Families/SubwordMemory/History.lean)
derives current/prior clock inputs and complete original Clean consistency from
actual Sail seeds and native matching. No shared semantic definitions or original
Sail clauses change. Canonical values/key binding and instruction execution remain
separate subword obligations.

## Subword initialized value preservation

[Full native decoder membership](Decoder/SubwordMemory.lean) now feeds the
[initialized payload-bound claim](../Trace/Families/SubwordMemory/Values.lean).
The unchanged shared value induction uses native local preservation from both
source and old-destination/RAM reads. Exact raw-key components and disjoint byte
contributions derive whole store-write bounds; actual original decoding derives
funct3/x0 ranges. [Same-state regressions](../../../Tests/SubwordWordBounds.lean)
retain actual public code/seed bytes. Shared Clean/Sail definitions, tables and
logical history semantics are unchanged; original instruction execution remains
separate.

## Subword native address geometry

[Original subword decoder membership](Decoder/SubwordMemory.lean) and the
unchanged initialized value induction now supply source/immediate/raw/x0 ranges
for [native address geometry](../Trace/Families/SubwordMemory/Address.lean).
The exact native offset relation and carry equations derive the containing
aligned word and actual mixed-port addresses. No helper table identity or
per-row expected address/read is supplied. Shared Clean/Sail semantics and
all original native fixed tables remain unchanged.

## Native subword load extensions

[Unchanged shared extension/extraction arithmetic](../../Proofs/SubwordMemory/ByteMath.lean)
now feeds [the initialized load-value claim](../Trace/Families/SubwordMemory/Loads.lean)
through exact v2 native keys and derived controls. Native ROM indexing and actual
RAM word ranges are derived; the odd discarded-load waiver remains explicit.
No native v3 key/table identity, table equivalence or expected read/result is
supplied. Original architectural access/exception/retirement remains separate.

## Native subword store byte windows

[Pure byte arithmetic](../../Proofs/SubwordMemory/StoreBytes.lean) adapts the
pinned v3 mathematical merge argument at default resource settings.
[The initialized native store claim](../Trace/Families/SubwordMemory/Stores.lean)
connects it to actual v2 clearing/placement keys, complete literal table outputs
and derived native selectors. SH alignment comes from the actual offset mask
and original decoding. No native v3 table/field identity or desired write is
assumed. Original architectural memory access/exception/retirement is separate.

## Actual reduced memory transfers

[The transfer observable](Memory/ReducedMachineWordMemoryTransfers.lean) records
original same-pre-state GPR/RAM/ROM reads, retained OLDREADs and actual writes,
plus chronological histories/numerical effects. [Its short public root](../Trace/Families/ReducedMachine/WordMemoryTransfers.lean)
derives these from exact NativeROM input construction, independent public shadow
seeds/full original decoding/native acceptance, aligned tracked cells and code
capacity. No local desired read/state/result or initial CSR premise. Retained
LOAD/STORE virtual-memory/platform/privilege clauses and instruction execution
remain separate; shadow values never become architectural ROM reads.

[Actual reduced memory platform inputs and clause observables](Memory/ReducedMachineWordMemoryPlatform.lean)
keep initial Machine/PMP/PMA/environment/hart/HTIF configuration conditional on a
nonempty original memory program. Public tracked RAM-cell domains exclude pinned
special windows; all local addresses/CSR reads/success derive from actual bounds/
matching/past history. [The clause root](../Trace/Families/ReducedMachine/WordMemoryClauses.lean)
retains original LOAD/STORE and unmasked x0 loads; no per-row desired answer.
These reference inputs do not prove native/physical enforcement. Empty programs
and the earlier transfer boundary remain CSR-free; normal/fetched memory is next.

[Actual reduced LW/SW normal/fetched execution](../Trace/Families/ReducedMachine/WordMemoryFetchedExecution.lean)
now discharges every local transfer/configuration/address/replay/state/order/PC
obligation from the existing meaningful public memory interfaces. Original
unmasked x0 loads and actual stores survive derived PC bookkeeping. Full native
shadow matching remains; architectural terminal readers are filtered. Empty
programs stay CSR-free. Common mixed memory/general physical enforcement remain
separate; helper input meanings and original Sail semantics are unchanged.

The [worker auxiliary roots](../Circuits/Blake2Worker/AuxiliaryTheorems.lean) now telescope all43 native memory factors
across the selected full domain under an explicit individual normalized auxiliary
acceptance contract and actual first/last public-claim boundaries. Separate typed
quartic slots, no division or terminal claim1. Product balance does not prove
full token matching/initialization or a delegation ledger; active ranges/keys/raw
clocks and issuance/converse/accounting remain open. No main frame crosses an
unproved delegated action, and physical enforcement stays separately scoped.

The [worker delegation sum roots](../Circuits/Blake2Worker/DelegationTheorems.lean) derive ordinary auxiliary sums from
native polynomial divisibility/degree/domain/sample inputs and normalize the
unified statement's returned-claim accumulator component. Main claims remain
opaque until their actual caller auxiliaries are connected; scalar balance is
not issuance/matching/converse/accounting. Physical/global capacity/dispatch/
challenge boundaries and active initialized memory effects remain open.

The [main caller auxiliary roots](../Circuits/ReducedMachine/DelegationTheorems.lean) now derive main claims from all native
ordinary-row auxiliary values and connect them to worker-row scalar sums. Separate
quartic92 and body92 roles remain explicit. Full body acceptance here does not
require every row active; existing initialized logical trace/history roots remain
unchanged. No inactive contribution is discarded, and padding/filter/matching,
global sequence/capacity/dispatch/challenge boundaries and accounting stay open.

The [configured caller/worker component](../Circuits/ReducedMachine/ConfiguredDelegationTheorems.lean) now retains the selected native
sequence/type/setup/shared-challenge checks and configured-slot counter over the
same returned proofs as the full-row scalar balance. Processing acceptance
derives Boolean indicators and an exact canonical multiplicity count below the
field modulus, with at most2048 selected proofs. No inactive auxiliary value is
dropped; capacity is not an issued count or matching/accounting certificate.
Initialized padding/filter/history, full43-token matching, active key/read/clock
refinement and physical/global transcript/setup/dispatch enforcement remain open.

The [native public memory-boundary component](../Circuits/ReducedMachine/MemoryBoundaryTheorems.lean) combines all selected worker
read/write products with the actual returned-main-claim fold and32-register/PC
source contributions. Public full32-bit values split before field casting;
x0 timestamps and PC initial time4 remain. Successful inverse-operation relations
clear only boundary denominators, retaining zero worker factors. Main grand
claims still need actual main state/memory/masking/initialization auxiliary
bindings; product balance does not establish token matching or initialized
histories/active bounds/accounting. Existing logical execution scopes remain.

The [actual main auxiliary component](../Circuits/ReducedMachine/MainAuxiliaryTheorems.lean) now derives returned main claims
from full ordinary-row memory/state/masking/initialization products, preserving
the actual execute polynomial and unmasked initialization. Same returned claims
compose with full worker products and public register/PC contributions without
factor cancellation or an execute-one premise. Token matching, initialization/
active bounds and faithful caller padding/filter/history remain open; existing
logical execution scopes and physical/general refinement boundaries are unchanged.
