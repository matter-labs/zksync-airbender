# Worker execution and complete references

This directory states what native worker accesses mean in actual Sail states and
how successive worker calls implement selected operation or hash references.
Bigint claims cover selected operation effects; the hash claims additionally cover
complete protocol spans. Worker execution is distinct from retiring the caller's
instruction or validating its full CSR ABI.

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
