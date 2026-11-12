# Production machine targets

[Theorems.lean](Theorems.lean) states the three production targets:
`UnrolledFullUnsigned`, `UnrolledReduced` and `Unified`.
The [final proofs](../../../../proven/Proven/Final/Trace/Machine/Unrolled.lean) establish both unrolled targets.
The [unified proof](../../../../proven/Proven/Final/Trace/Machine/Unified.lean) establishes the unified target.

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
The [unrolled](../../../../proven/Proven/Trace/Machine/UnrolledStandardCycle.lean) and
[unified](../../../../proven/Proven/Trace/Machine/UnifiedStandardCycle.lean) caller proofs give actual fetched RV steps
for bigint, G and round cycles. They derive reads, write values and distinct worker addresses from shared matching.
The round proof accepts every native Boolean mask.
The ordinary [unrolled](../../../../proven/Proven/Trace/Machine/UnrolledOrdinaryCycle.lean) and
[unified](../../../../proven/Proven/Trace/Machine/UnifiedOrdinaryCycle.lean) cycles reuse the existing family proofs
with actual shared-history reads, including branches and jumps.
The [unrolled](../../../../proven/Proven/Trace/Machine/UnrolledModularStep.lean) and
[unified](../../../../proven/Proven/Trace/Machine/UnifiedModularStep.lean) modular row proofs give RV instruction steps
for all four field operations. The [discarded-destination proofs](../../../../proven/Proven/Trace/Machine/ModularZeroStep.lean)
cover their x0 preprocessing.
The [shared memory proof](../../../../proven/Proven/Trace/Machine/MemoryBounds.lean) bounds every CPU and worker read,
write and terminal word from the public seeds and native matching. The transfer-order proof covers both worker pools.
The [history proof](../../../../proven/Proven/Trace/Machine/SharedHistory.lean) gives one actual RV memory history
and its terminal reads. Native caller zeroes and public decoder metadata preserve x0.
The [cycle partition](../../../../proven/Proven/Trace/Machine/CycleGroups.lean) retains each CPU row and its unique
matched standard or split worker. It uses occurrence clocks and permits repeated PCs.

The native acceptance interface is explicit. The [run composition](../../../../proven/Proven/Trace/Machine/UnrolledRun.lean)
uses one shared history and permits loops. The [padded targets](Padding.lean) use the native contribution mask
for CPU, worker, state, request and memory tuples. Their [proofs](../../../../proven/Proven/Final/Trace/Machine/Padding.lean)
erase identity factors and retain full occurrence counts. Cached GKR preservation remains open.

[Hash segmentation](Segmentation.lean) partitions complete G, round and split Keccak windows by native occurrence clocks.
Its public window interface supplies caller coverage, protocol counts and CSR families.
The [proof](../../../../proven/Proven/Final/Trace/Machine/Segmentation.lean) derives worker coverage, unique assignment,
full request multiplicity and the total call count. Active zero-clock workers are rejected.

The [code-bound segmentation claims](CodeWindows.lean) derive caller counts and CSR families from public decoded entries,
native clock density and the protocol duration. Their [proofs](../../../../proven/Proven/Final/Trace/Machine/CodeWindows.lean)
need no worker count or expected output. Occurrence coverage and ordered public intervals remain explicit.
