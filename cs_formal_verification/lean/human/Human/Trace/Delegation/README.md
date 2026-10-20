# Caller and worker composition

This directory states composition relations between decoded callers, matched
worker requests and shared memory histories. Its conclusions include actual port
execution, terminal-token agreement and complete reference effects for selected
spans. Those relations retain protocol/prefix conditions and do not by themselves
establish full mixed instruction retirement.

## Checked results

[`requests_soundness` and `worker_schedule_soundness`](../../../../slop/Slop/Final/Trace/Delegation/CallerTheorems.lean) bind
original public caller decoding to the request permutation and derive unique
issued-worker placement inside the caller's four-tick cycle. Zero-clock workers
remain classified as unissued; the claims do not exclude their prefix effects.

[`shared_memory_soundness`](../../../../slop/Slop/Final/Trace/Delegation/CallerTheorems.lean) proves callers and workers execute
in one initialized GPR/RAM history. [`shared_operation_soundness`](../../../../slop/Slop/Final/Trace/Delegation/CallerTheorems.lean)
adds the selected operation references and derived bounds; the
[logical memory result](../../Helpers/Memory/README.md#logical-memory-result)
explains the history implication.

[`shared_span_soundness` and `request_hash_window_soundness`](../../../../slop/Slop/Final/Trace/Delegation/CallerTheorems.lean)
bind complete selected references and actual terminal/cut states under their
public protocol, count, domain/table and matching inputs.
The full caller-control ABI and whole mixed retirement remain separate.

Read [CallerTheorems](../../../../slop/Slop/Final/Trace/Delegation/CallerTheorems.lean) and [Theorems](../../../../slop/Slop/Final/Trace/Delegation/Theorems.lean) for
the public claims. Their shared inputs live in
[Helpers/Delegation](../../Helpers/Delegation/README.md).

[Execution](Execution.lean), [SharedMemory](SharedMemory.lean) and
[MixedMemory](MixedMemory.lean) expose actual Sail histories and terminal-token agreement.
[RequestTrace](RequestTrace.lean) and [RequestEffects](RequestEffects.lean)
connect decoded callers to matched worker observations.
[SharedOperations](SharedOperations.lean) uses the existing worker references.

[SharedSpans](SharedSpans.lean), [HashWindows](HashWindows.lean) and
[RequestHashWindows](RequestHashWindows.lean) compose complete protocols and
selected caller/worker regions. Native cuts retain boundary timestamps.
Exact multiplicity, slots and controls must follow from the same accepted history.

Keep each theorem's public protocol ABI, span counts and prefix scope visible.
An active zero-clock worker may affect the prefix without an issued caller.
Bigint invalid controls and worker ROM shadows remain genuine gaps.
These claims do not establish full CSR semantics, whole mixed instruction
retirement or cryptographic request/memory enforcement.
