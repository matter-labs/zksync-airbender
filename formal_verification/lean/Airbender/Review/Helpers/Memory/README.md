# Native memory and initialized history

This directory models native register/RAM transfers with their addresses, values
and retained timestamps, starting from an independent public Sail image. Its
history relations connect those transfers to actual Sail states. Native zero ROM
shadows and public ROM bytes remain separate representations, linked only where a
claim supplies the required view conversion.

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
  predicate. The separately connected Sail history realizes the native transfers
  and their terminal values under its public-image/domain conditions.

| Result | Proof |
| --- | --- |
| Complete per-address chains | [`native_memory_paths`](../../../Proofs/Trace/MemoryPaths.lean) |
| Latest preceding write for every read | [`latest_reads`](../../../Proofs/Trace/LatestReads.lean) |
| Complete Clean-consistent history | [`native_memory_history`](../../../Proofs/Trace/MemoryHistory.lean) |
| Clock conditions from imported constraints | [`ClockLaws`](../../../Proofs/Trace/History.lean) |
| Actual Sail interpretation | [native history transport](../../../Proofs/Trace/NativeSailHistory.lean) |

The generic history result retains its public-image and domain conditions.
The [native initialization adapters](../../Trace/Initialization.lean) derive
computed seed correspondence, selected-domain uniqueness/alignment and coverage
of all 32 registers from the native boundary geometry. The public Sail state,
program/configuration and initial register profile remain inputs, with register
boundary/teardown obligations separate from the RAM-only GKR slices. See the
[initialization guide](../../Circuits/Initialization/README.md).

Exact logical token matching remains a separate memory-argument boundary. The
initialization GKR proofs establish encoded token products; equality of sampled
products does not deterministically imply full token-multiset equality or prove
cryptographic soundness. Worker ROM/public-byte binding and global inactive-row
obligations also remain separate; a consistent memory history does not by itself
validate an instruction or a caller's control word.

Start with [InitialImage](InitialImage.lean) for actual public Sail GPR/byte reads
and the tracked cell domain. [Initialization](Initialization.lean) describes the
boot profile; [Platform](Platform.lean) records the ordinary-memory configuration.

[Ports](Ports.lean) and [IndirectPorts](IndirectPorts.lean) interpret imported
addresses, timestamps and values. [Values](Values.lean) gives the word view.
[History](History.lean) states logical native events and matching; its rows and
tokens come from the shared [`model`](../Context/Model.lean).

[SailHistory](SailHistory.lean) connects those transfers to actual Sail states.
Bounds and latest-write reads are derived by the supporting proofs from accepted
constraints, preserved writes and public initialization; desired reads are not supplied.

[ROM](ROM.lean) models public word-ROM tables. [Native](Native.lean) keeps the
prover's zero ROM shadows separate from actual public bytes and names the view conversion.
Check the claim's tracked domain, alignment, platform, seed timestamps and terminal tokens.

Logical matching is explicit; this is not a cryptographic memory-argument proof.
The checked [worker ROM boundary](../../../../Tests/DelegationROMBoundary.lean)
prevents silently replacing worker shadows with public bytes.
Whole-run terminal realization belongs in [Trace](../../Trace/README.md).
