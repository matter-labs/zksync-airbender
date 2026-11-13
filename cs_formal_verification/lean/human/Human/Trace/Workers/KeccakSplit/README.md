# Split Keccak permutation

The split Keccak workers in initialized memory: what each call does to the `RV.State` and that
a complete request computes Keccak-f[1600].

## Checked results

| Claim | Direct theorem entry |
| --- | --- |
| Every access executes on the `RV.State`; every row is a call of the schedule | [`Native.rv_operation_execution`](../../../../../proven/Proven/Final/Trace/Workers/KeccakSplit/RVTheorems.lean) |
| A 361-call request executes call by call and writes the permutation | [`Native.rv_permutation_soundness`](../../../../../proven/Proven/Final/Trace/Workers/KeccakSplit/RVTheorems.lean) |

Read [RVTheorems](RVTheorems.lean), [RVInputs](RVInputs.lean) and [Execution](RVExecution.lean).
`RVOperationInputs` and `RVCallInputs` give initialized memory (`RVMemoryInputs`, with the
approved invocation-high assumption), active rows and, for a request, x10 starting
at 0 and 361 calls. Matching derives everything else: the call order and controls,
the shared x11 pointer and its alignment, every read and its range, and one
`Call.RVExecutesAt` per call between consecutive actual RV states. The result is
stated with the special5 `Keccak.Permutation.RVWordMapping` and Clean's
`keccakPermutation`. Connecting a request to the calling instructions is the
request-binding task, as for the other workers.
