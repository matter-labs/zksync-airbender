# Native memory and initialized history

This directory models native register/RAM transfers with their addresses, values
and retained timestamps, starting from an independent public `RV.State` image. Its
history relation (`RVHistory`) connects those transfers to actual `RV.State`s. Native zero ROM
shadows (RAM cells below `ROM_END` in the spec) and public ROM bytes (the ROM image) remain
separate representations.

## Logical memory result

The [acceptance model](../Context/Model.lean) assumes exact multiset matching:

```text
initial tokens + new/write tokens = previous/read tokens + terminal tokens
```

Each token includes the full address, timestamp and value. Readonly accesses
also create new tokens: they preserve the value and refresh its timestamp.

Together with one public seed per address, the stated field/inverse conditions
and public initial-clock bounds/alignment, accepted constraints force strict
previous-to-new timestamp growth. The clock laws are proved for the imported
family layouts; an expected read or preconstructed memory history is not supplied.
Permutation equality alone is insufficient without these conditions.

The checked conclusions are:

- Every access belongs to a complete chronological chain from its address's
  initial token to its terminal token; all accesses are included.
- Every read takes its value from the latest preceding write, or initialization
  before the first write. Uninitialized, fabricated or stale reads cannot meet
  the full conditions; disconnected cycles and branching cell histories are excluded.
- These chains form a history satisfying Clean's original online-consistency
  predicate. The separately connected RV history realizes the native transfers
  and their terminal values under the public-image/domain conditions.

| Result | Proof |
| --- | --- |
| Complete per-address chains | [`native_memory_paths`](../../../../slop/Slop/Trace/MemoryPaths.lean) |
| Complete Clean-consistent history (every read takes the latest preceding write or the initial value) | [`native_memory_history`](../../../../slop/Slop/Trace/MemoryHistory.lean) |
| Clock conditions from imported constraints | [`ClockLaws`](../../../../slop/Slop/Trace/History.lean) |
| Actual RV interpretation | [`RVHistory`](RVHistory.lean) executes the events on an `RV.State`; the [history split](../../../../slop/Slop/Trace/HistorySplit.lean) cuts it at a clock |

This result covers the ports included by the selected model. Public initialization
and exact matching remain conditions. Native unified ROM-shadow transport and global
inactive-row obligations remain separate; a consistent memory history does not
by itself validate an instruction or a caller's control word.

Start with [InitialImageRV](InitialImageRV.lean) for the public `RV.State` register and
RAM reads and [InitialImage](InitialImage.lean) for the tracked cell domain. The boot profile
(PC 0, zero registers, RAM seeded by the inits/teardowns Init tokens) is `RVPooledBootInputs`
in [Context](../Context/README.md); there is no machine-configuration or Sail memory-map premise.

[Ports](Ports.lean) and [IndirectPorts](IndirectPorts.lean) interpret imported
addresses, timestamps and values. [Values](Values.lean) gives the word view.
[History](History.lean) states logical native events and matching; its rows and
tokens come from the shared [Model](../Context/Model.lean).

[RowEvents](RowEvents.lean) defines the native row events (ports with their shifted clocks);
[RVHistory](RVHistory.lean) and [RVAtomicWrites](RVAtomicWrites.lean) execute them on an `RV.State`.
Bounds and latest-write reads are derived by the supporting proofs from accepted
constraints, preserved writes and public initialization; desired reads are not supplied.

[ROM](ROM.lean) models public word-ROM tables from the ROM image (`romImageRV`). [Native](Native.lean) names the
prover's zero ROM shadows, which are RAM cells below `ROM_END` in the spec.
Check the claim's tracked domain, alignment, seed timestamps and terminal tokens.

Logical matching is explicit; this is not a cryptographic memory-argument proof.
In the spec only delegations reach the shadow RAM below `ROM_END`, and the ROM image is never written; the
[COPY fixture](../../../../test/Tests/DelegationROMBoundary.lean) has a worker port addressing such a cell.
Whole-run terminal realization belongs in [Trace](../../Trace/README.md).
