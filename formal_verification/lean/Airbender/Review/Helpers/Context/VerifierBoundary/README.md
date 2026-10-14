# Canonical verifier PC boundary

[Model](Model.lean) separates typed external statement words from the logical
binding to imported PC-state tuples. [Theorems](Theorems.lean) proves the encoding
and derives raw terminal bounds. The implementation is in
[Proofs/VerifierBoundary](../../../../Proofs/VerifierBoundary.lean).

`Endpoint` contains a 32-bit PC and two 32-bit timestamp words. `Endpoint.encode`
reuses the low/high PC split in `PCState.boundary`. For a field larger than 65536,
both PC limbs are below 65536 and their interpreted word is exactly the supplied
PC. Timestamp words are cast with reduction, matching the inspected Rust path;
this does not assert an additional timestamp range.

`Binding` states that the trace's initial tuple equals the encoded initial
statement and that the encoded initial contribution plus the actual row ends
permutes to the encoded final contribution plus the actual row starts. It keeps
both original PC columns and timestamp columns separately. Comparing this closure
with accepted native state matching and canceling the identical start-list proves
full raw terminal-tuple equality with the encoded final contribution. No raw PC
pair is reduced or repacked to manufacture this equality.

`Closure` supplies such a typed statement and binding. `BootClosure` additionally
fixes the initial PC/clock to 0/4, as in the inspected total-verifier paths. Other
typed initial endpoints describe explicitly conditional canonical trace/segment
scopes; no general Rust verifier with arbitrary initial endpoints is asserted.

| Checked result | Public theorem |
| --- | --- |
| Bounded PC limbs and full u32 PC preservation | [`encoding_soundness`](Theorems.lean) |
| Equality of the original terminal tuple after permutation cancellation | [`terminal_state_soundness`](Theorems.lean) |
| Actual imported terminal-PC bounds from accepted matching and boundary closure | [`terminal_bound_soundness`](Theorems.lean) |

The per-row jump/branch/comparison `TraceInputs`, standalone jump
`ExecutionBoundary` and physical `PooledInputs` consume the general closure.
`PooledBootInputs` consumes the boot closure, which survives ROM interpretation
because every imported row start/finish is preserved. These public inputs replace
their former direct terminal-range premises. Local calculation and range lemmas
remain conditional. The unified artifact retains its separately proved local
output ranges and its existing public scope. `PCState.Context.terminalPC` remains
a typed `BitVec` field in the abstract shared interface; the former raw terminal
range fields are absent from these public input records.

## Inspected source and external obligations

The inspected checkout revision is
`0dc0a631349462700825f326516d36200be30edc`, with no local changes to these Rust
files. This Lean change makes no Rust behavior change.

| Source | Inspected mechanism |
| --- | --- |
| [Unrolled statement](../../../../../../../full_statement_verifier/src/unrolled_proof_statement.rs) | Lines 75–83 read the final PC/timestamps; 239–253 incorporate boundary contributions and compare global products. Blob `d79920d3f554a9457b9bdee4d722150cda1bde13`. |
| [Unified statement](../../../../../../../full_statement_verifier/src/unified_circuit_statement.rs) | Lines 73–81 and 247–261 use the same mechanism. Blob `57bf2f6325651f6bdb46de18f6435f6953b5fb4e`. |
| [Contribution encoder](../../../../../../../prover/src/definitions/mod.rs) | Lines 8–11 split a u32 using mask/shift; 269–302 encode PC low/high with distinct machine-state challenge coefficients, PC address space and timestamp fields. Blob `0321500837083cc700bd23893a75c6b7fcbf3194`. |
| [Challenge indices](../../../../../../../cs/src/definitions/constants.rs) | Lines 19–35 alias the PC low/high coefficients to the corresponding memory-value coefficients, with the same timestamp coefficients. Blob `25d575306df03fa3869afa927abbc756c28e8f4a`. |
| [GKR memory compiler](../../../../../../../cs/src/gkr_compiler/memory_like_grand_product.rs) | Lines 478–502 place start/end PCs as separate u16-limb values in PC-space read/write tuples. Blob `6f4ae37c6c8643f5f2aac40b399502ea10699ffb`. |
| [Initial PC](../../../../../../../common_constants/src/lib.rs), [initial timestamp](../../../../../../../common_constants/src/timestamps.rs) | Public constants are PC zero and timestamp four. |

The supplied historical revision `1f4a8455e9f893a1ffb3d23ad79918f243b28aca`
was not inspected: its source blob could not be retrieved. The provenance above
refers to the actual local checkout, not that revision or every verifier variant.

`Binding` is an explicit logical contract, not a proved Rust acceptance predicate.
Cryptographic enforcement of exact tuple matching, PC-space projection from the
global argument, import/setup fidelity and Rust/compiled-artifact correspondence
remain external. Product equality at sampled challenges is not deterministic
multiset equality. No cryptographic soundness or verifier refinement is proved.

The [original F01 witness](../../../../../Tests/JumpSailHistory.lean) remains
accepted by its local/logical relation; `noncanonical_verifier_boundary_rejected`
excludes it from every new canonical boundary closure. The
[valid JALR fixture](../../../../../Tests/JalrTrace.lean) proves
`canonical_verifier_boundary` and instantiates the public standalone trace and
per-circuit soundness claims. Existing branch/comparison and pooled fixtures also
inhabit the replacement contracts.
