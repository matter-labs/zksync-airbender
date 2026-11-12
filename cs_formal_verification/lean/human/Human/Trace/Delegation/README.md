# Caller and worker composition

The RV delegation spec follows the circuit for invalid controls and worker RAM pointers.
These inputs have undefined VM behavior; separate validity conditions delimit the reference-agreement claims.

This directory states composition relations between decoded callers, matched
worker requests and shared memory histories. Its conclusions include actual port
execution, terminal-token agreement and complete reference effects for selected
spans. Those relations retain protocol/prefix conditions and do not by themselves
establish full mixed instruction retirement.

## Checked results

Every caller claim also has a `…SatisfiableClaim` beside it, witnessed by caller traces with matched workers (a bigint
call, an ordinary preparation row, a complete 56-call G span) in [Satisfiable/Callers](../../../../proven/Proven/Final/Trace/Satisfiable/Callers.lean).

[`rv_requests_soundness` and `rv_worker_schedule_soundness`](../../../../proven/Proven/Final/Trace/Delegation/RVCallerTheorems.lean) bind
public caller decoding (`RV.decode` to `.delegate k`) to the request permutation and derive unique
issued-worker placement inside the caller's four-tick cycle. Zero-clock workers
remain classified as unissued; the claims do not exclude their prefix effects.
The upstream circuits reject an active zero-clock row (timestamp query 0,
[regression](../../../../test/Tests/DelegationZeroInvocation.lean)); the claims do not use this.

[`rv_shared_memory_soundness`](../../../../proven/Proven/Final/Trace/Delegation/RVCallerTheorems.lean) proves callers and workers execute
in one initialized GPR/RAM history on an `RV.State`. [`rv_shared_operation_soundness`](../../../../proven/Proven/Final/Trace/Delegation/RVCallerTheorems.lean)
adds the selected operation references and derived bounds; the
[logical memory result](../../Helpers/Memory/README.md#logical-memory-result)
explains the history implication.

[`rv_shared_span_soundness` and `rv_request_hash_window_soundness`](../../../../proven/Proven/Final/Trace/Delegation/RVCallerTheorems.lean)
bind complete selected references and actual terminal/cut states under their
public protocol, count, domain/table and matching inputs. A complete span's final state is the
spec's run of its delegation calls (`RV.calls`), up to the PC advance.
The full caller-control ABI and whole mixed retirement remain separate.

Read [RVCallerTheorems](RVCallerTheorems.lean) and [RVTheorems](RVTheorems.lean) for
the public claims. Their shared inputs live in
[Helpers/Delegation](../../Helpers/Delegation/README.md).

[RVExecution](RVExecution.lean), [RVSharedMemory](RVSharedMemory.lean) and
[RVMixedMemory](RVMixedMemory.lean) expose actual RV histories and terminal-token agreement.
[RVRequestTrace](RVRequestTrace.lean) and [RVRequestEffects](RVRequestEffects.lean)
connect decoded callers to matched worker observations; the shared operations use the existing worker references.

[RVSharedSpans](RVSharedSpans.lean), [RVHashWindows](RVHashWindows.lean) and
[RVRequestHashWindows](RVRequestHashWindows.lean) compose complete protocols and
selected caller/worker regions. Native cuts retain boundary timestamps.
Exact multiplicity, slots and controls must follow from the same accepted history.

Keep each theorem's public protocol ABI, span counts and prefix scope visible.
The claims still admit unissued prefix effects; the circuit's query 0 rejects active zero-clock rows.
The bigint invalid-control gap remains.
These claims do not establish full CSR semantics, whole mixed instruction
retirement or cryptographic request/memory enforcement.
