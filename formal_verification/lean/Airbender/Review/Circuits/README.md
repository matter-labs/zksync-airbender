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
