# Worker execution and complete references

This directory states what native worker accesses mean in actual Sail states and
how successive worker calls implement selected operation or hash references.
Bigint claims cover selected operation effects; the hash claims additionally cover
complete protocol spans. Worker execution is distinct from retiring the caller's
instruction or validating its full CSR ABI.

## Checked results

All four native worker families have selected reference effects on actual Sail
port reads/writes in initialized shared memory; operand/address bounds are derived.
The hash results additionally bind complete initial/final blocks or lanes and
native terminal tokens, with schedules and intermediate values derived from matching.

| Claim | Direct theorem entry |
| --- | --- |
| Seven selected bigint operation effects | [`Airbender.Bigint.Native.operation_execution`](Bigint/Theorems.lean) |
| Complete G work-vector fold | [`Airbender.Blake2G.Native.workvector_soundness`](Blake2G/Theorems.lean) |
| Complete extended-BLAKE compression | [`Airbender.Blake2Round.Native.compression_soundness`](Blake2Round/Theorems.lean) |
| Complete Keccak permutation | [`Airbender.Keccak.Native.permutation_soundness`](Keccak/Theorems.lean) |

Native-boundary/window variants retain timestamps rather than restarting history.
Public protocol modes/counts, modeled tables, domain/alignment and the existing
worker ABI conditions remain visible. A standalone extended-round operation still
takes its mask ABI; prepared unified scopes derive those masks.
Worker-only [MemoryInputs](../../Helpers/Delegation/Memory.lean) and
[BoundaryMemoryInputs](../../Helpers/Delegation/BoundaryMemory.lean) expose both
`MemoryInputs.clockRoom` (the low invocation limb leaves room for offset-two writes) and
`MemoryInputs.invocationHigh` (the high limb is in range). The integrated caller/request
matching derives these bounds and complete participation; the current worker
compiler does not independently query the invocation high limb. These inputs
supply neither read values nor pointer bounds: initialized matching derives them.

These worker claims do not alone prove full CSR validity.
[Unified native-path execution](../UnifiedReduced/NativePathExecution.lean)
composes caller retirement through branches, jumps and loops under the
[F11 hash witness contracts](../../../../FINDINGS.md#f11--hash-witness-contracts-remain-unenforced),
F02 bigint commands and the stated RAM/configuration profile. Complete grouped
algorithms additionally require per-trace protocol coverage and valid memory gaps.

These directories connect local worker behavior to actual Sail port observations
and, for the hash families, complete protocol spans.

| Family | Review entry | Complete scope |
| --- | --- | --- |
| Bigint | [Guide](Bigint/README.md) | Seven selected operation references; full caller-control ABI remains open. |
| BLAKE2 G | [Guide](Blake2G/README.md) | The pinned 56/80-call work-vector fold. |
| Extended BLAKE | [Guide](Blake2Round/README.md) | Seven-/ten-round compression. |
| Keccak | [Guide](Keccak/README.md) | The complete 649-call permutation span. |

Start with the public theorem and its input record. Check actual initial/final
reads, native seed timestamps, tracked domain, modeled tables and logical matching.
Schedules, operand bounds and intermediate states are derived from that history.

A complete worker protocol is distinct from a caller's instruction retirement.
[Delegation composition](../Delegation/README.md) and
[unified windows](../UnifiedReduced/README.md) bind the selected shared scopes.
Unissued-worker, bigint-control and ROM-shadow counterexamples remain visible.
