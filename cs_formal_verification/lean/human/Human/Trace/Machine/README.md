# Production machine targets

[Theorems.lean](Theorems.lean) states the three production targets:
`UnrolledFullUnsigned`, `UnrolledReduced` and `Unified`.
The statements are targets. Their proofs are open.

Each conclusion is `RVRealizes`: one run of `RV.run` reaches the terminal PC and tracked cells.
The program is public ROM data. Each initialization instance supplies its own checked top bits.
[Model.lean](Model.lean) states the native constraint, decoder, request, state and memory interfaces.
The standard and split worker pools share the architectural memory permutation.
The [input interface](ExternalInput.lean) binds actual response ports to the independent stream in the initial state.
The input values are external data. The circuit does not authenticate the stream.

The full target includes split Keccak and excludes special5. It excludes `mop.r.N` because the full
machine uses a plain rotate and the current RV spec uses xor-rotate.
Delegation validity is not a target premise. Invalid controls and worker pointer use follow the delegation spec.
The typed [verifier boundary](../../Helpers/Context/VerifierBoundary/Theorems.lean) derives terminal-PC bounds.
Its raw tuple and range claims have separate witnesses.
The [malformed-PC regression](../../../../test/Tests/VerifierBoundary.lean) checks native acceptance and verifier rejection.

Native initialization gates imply the exact token products through the imported artifact bindings.
The [bigint](../../../../proven/Proven/UnifiedReduced/RVCaller/BigintStep.lean),
[G](../../../../proven/Proven/UnifiedReduced/RVCaller/GStep.lean) and
[round](../../../../proven/Proven/UnifiedReduced/RVCaller/RoundStep.lean) caller proofs give local RV steps.
The round proof accepts every native Boolean mask.
The [shared memory proof](../../../../proven/Proven/Trace/Machine/MemoryBounds.lean) bounds every CPU and worker read,
write and terminal word from the public seeds and native matching. The transfer-order proof covers both worker pools.
The [history proof](../../../../proven/Proven/Trace/Machine/SharedHistory.lean) gives one actual RV memory history
and its terminal reads. Native caller zeroes and public decoder metadata preserve x0.
The [cycle partition](../../../../proven/Proven/Trace/Machine/CycleGroups.lean) retains each CPU row and its unique
matched standard or split worker. It uses occurrence clocks and permits repeated PCs.

The native acceptance interface is explicit. Cached GKR preservation, whole execution composition
and padding remain open before these targets have final proofs.
