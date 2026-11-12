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

The native acceptance interface is explicit. Cached GKR preservation, full execution composition,
padding and initialization-gate binding must discharge the open parts before these targets have final proofs.
