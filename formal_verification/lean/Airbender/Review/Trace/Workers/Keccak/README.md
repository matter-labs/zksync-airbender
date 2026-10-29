# Complete special5 Keccak permutation

<!-- source-names: keccak_special5 keccak_f1600 -->

This directory states the complete permutation effect of a 649-call Keccak span,
binding Clean's original reference to actual initial/final lane reads. Call and
window contracts retain seed timestamps and protocol scope, while shared execution
connects the final state to native terminal tokens.

This is conditional coverage of `keccak_special5`. The provided `keccak_f1600`
wrapper uses 361 calls to three split circuits, which are absent from the
inspected unified setup's CSR allowlist. The
[split schedule](SplitSchedule.lean) and its
[proofs](../../../../Proofs/Keccak/SplitSchedule.lean) establish the exact
24-round/final-call order, call counts and control progression. The three
[split caller forms](../../../Helpers/Delegation/SplitCaller.lean) retain the
full virtual CSR and original Sail instruction. Their
[public code-shape interface](SplitUse.lean) requires all 361 positions and
complete caller coverage, safe initial entry, and the reference x10 control and
256-byte-aligned x11 state pointer without assuming worker outputs. The three
cached and no-cache compiled circuits now have native imports for their equations, fixed
lookups and timestamp queries: [column parity](../../../Circuits/Keccak/SplitColumnParity.lean),
[theta/rho](../../../Circuits/Keccak/SplitThetaRho.lean) and
[chi5](../../../Circuits/Keccak/SplitChi5.lean), with their cached variants in the same directory. Theta/rho and chi5 preserve
grouped timestamp metadata, invocation columns and the native memory ports bound
to each checked group. The [split native interface](SplitNative.lean) now states
equations, participation and exact memory-token matching for all six captures.
The [split request interface](SplitRequests.lean) matches full-width native CSR
calls to worker invocation clocks under an explicit virtual-token permutation.
[Request proofs](../../../../Proofs/Keccak/SplitRequests.lean) derive one-to-one
nonzero fulfillment, clock bounds, no low-limb rollover, the worker kind
selected by the full-width public Sail CSR, and the caller's canonical PC
retirement. Complete setup provenance, caller/worker memory composition and
worker-effect proofs remain open.
Under the [ValidDelegationUse](../../UnifiedReduced/DelegationUse.lean) contract, special5 calls are
excluded; these lemmas therefore do not establish blessed Keccak execution.
Split worker modeling and integration are required open work. See
[F12](../../../../../FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage).

## Checked results

[`Native.operation_execution`](Theorems.lean) proves actual port/lane effects
for all seven native modes under the imported native controller.
[`Native.permutation_soundness` and `Native.permutation_boundary_soundness`](Theorems.lean)
prove the original full permutation on actual boundary lanes, with shared terminal
agreement. [`Native.window_soundness`](Theorems.lean) binds the first complete span
at retained cut states; later workers may remain outside the window.
Public protocol/domain/alignment/table conditions remain inputs.

[`Call.execution_soundness`](ReferenceCalls.lean) additionally executes the
independent [complete micro-call reference](../../../Circuits/Keccak/Call.lean)
in the actual full Sail states, with exact writes and frame. The existing
649-call schedule derives supported full controls; initialized history supplies
canonical lane reads and the aligned RAM pointer. It adds no per-row ABI or
expected-output premise. [Full mixed execution](../../UnifiedReduced/FullExecution.lean)
connects caller fetch/PC retirement with participation derived from native
caller accounting and active-invocation timestamps. That entrypoint retains its
straight-line ordinary registry. The newer
[native-path entrypoint](../../UnifiedReduced/NativePathExecution.lean) supports
branches, jumps and loops under the
[F11 hash witness contracts](../../../../../FINDINGS.md#f11--hash-witness-contracts-remain-unenforced).
[Complete spans](../../UnifiedReduced/PathSpanExecution.lean) retain a per-trace
protocol plan, complete coverage and valid gaps. No external occurrence ledger
is supplied to the native participation derivation.

Read [Theorems](Theorems.lean), [Call](Call.lean) and
[BoundaryCall](BoundaryCall.lean). [Permutation](Permutation.lean) binds
the original complete reference to actual initial/final lane reads.

[Windows](Windows.lean) selects the first complete 649-call span.
Initialized matching derives the control schedule, fixed pointer, lane/scratch
coverage and linked intermediate states. Keep native seed timestamps, modeled
controller tables, public domain and complete-span ABI visible.

[Local modes](../../../Circuits/Keccak/README.md) have a narrower scope.
Invalid-control fallback does not establish the 24-round protocol.
[Caller composition](../../Delegation/README.md) and
[prepared unified spans](../../UnifiedReduced/README.md) retain separate prefix
and preparation restrictions; completion does not imply automatic restart.

Standalone worker inputs retain both `clockRoom` and `invocationHigh`; integrated
caller/request matching derives them. See the [shared worker boundary](../README.md)
and [native memory inputs](../../../Helpers/Delegation/Memory.lean). Actual read
values and pointer bounds are derived from initialized matching.

The [independent known-answer regression](../../../../../Tests/KeccakKnownAnswer.lean)
checks Clean's 24-round permutation against the pinned XKCP all-zero vector
and NIST's FIPS 202 SHA3-256 empty-message permutation state, including lane
order. It does not establish split/special5 circuit coverage.
