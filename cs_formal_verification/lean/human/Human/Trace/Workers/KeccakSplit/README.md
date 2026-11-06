# Split Keccak permutation

The split Keccak workers in initialized memory: what each call does in Sail and that
a complete request computes Keccak-f[1600].

## Checked results

| Claim | Direct theorem entry |
| --- | --- |
| Every access executes in Sail; every row is a call of the schedule | [`Native.operation_execution`](../../../../../slop/Slop/Final/Trace/Workers/KeccakSplit/Theorems.lean) |
| A 361-call request executes call by call and writes the permutation | [`Native.permutation_soundness`](../../../../../slop/Slop/Final/Trace/Workers/KeccakSplit/Theorems.lean) |

Read [Theorems](Theorems.lean), [Inputs](Inputs.lean) and [Execution](Execution.lean).
`OperationInputs` and `CallInputs` give initialized memory (`MemoryInputs`, with the
approved invocation-high assumption), active rows and, for a request, x10 starting
at 0 and 361 calls. Matching derives everything else: the call order and controls,
the shared x11 pointer and its alignment, every read and its range, and one
`Call.ExecutesAt` per call between consecutive actual Sail states. The result is
stated with the special5 `Keccak.Permutation.WordMapping` and Clean's
`keccakPermutation`. Connecting a request to the calling instructions is the
request-binding task, as for the other workers.
