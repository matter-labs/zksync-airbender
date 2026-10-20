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
| Seven selected bigint operation effects | [`operation_execution`](../../../../slop/Slop/Final/Trace/Workers/Bigint/Theorems.lean) |
| Complete G work-vector fold | [`Native.workvector_soundness`](../../../../slop/Slop/Final/Trace/Workers/Blake2G/Theorems.lean) |
| Complete extended-BLAKE compression | [`compression_soundness`](../../../../slop/Slop/Final/Trace/Workers/Blake2Round/Theorems.lean) |
| Complete Keccak permutation | [`Native.permutation_soundness`](../../../../slop/Slop/Final/Trace/Workers/Keccak/Theorems.lean) |

Native-boundary/window variants retain timestamps rather than restarting history.
Public protocol modes/counts, modeled tables, domain/alignment and the existing
worker ABI conditions remain visible. A standalone extended-round operation still
takes its mask ABI; prepared unified scopes derive those masks.
These claims do not prove full CSR validity or whole mixed caller retirement.

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
