# Canonical verifier PC boundary

[Model](Model.lean) separates typed external statement words from the logical
binding to imported PC-state tuples. [Theorems](Theorems.lean) proves the encoding
and derives raw terminal bounds. The implementation is in
[Proofs/VerifierBoundary](../../../../Proofs/VerifierBoundary.lean).

`Endpoint` contains a 32-bit PC and two 32-bit timestamp words. `Endpoint.encode`
reuses the low/high PC split in [`Airbender.PCState.boundary`](../PCState/Model.lean). For a field larger than 65536,
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
| Bounded PC limbs and full u32 PC preservation | [`Airbender.VerifierBoundary.encoding_soundness`](Theorems.lean) |
| Equality of the original terminal tuple after permutation cancellation | [`terminal_state_soundness`](Theorems.lean) |
| Actual imported terminal-PC bounds from accepted matching and boundary closure | [`terminal_bound_soundness`](Theorems.lean) |

The per-row jump/branch/comparison
[`Airbender.JumpBranchSlt.TraceInputs`](../../../Circuits/JumpBranchSlt/Model.lean),
standalone jump [`Airbender.Trace.ExecutionBoundary`](../Boundary.lean) and physical
[`Airbender.Trace.PooledInputs`](../PooledBoundary.lean) consume the general closure.
[`Airbender.Trace.PooledBootInputs`](../PooledBoundary.lean) consumes the boot closure, which survives ROM interpretation
because every imported row start/finish is preserved. These public inputs replace
their former direct terminal-range premises. Local calculation and range lemmas
remain conditional. The unified artifact retains its separately proved local
output ranges and its existing public scope. [`Airbender.PCState.Context.terminalPC`](../PCState/Model.lean) remains
a typed `BitVec` field in the abstract shared interface; the former raw terminal
range fields are absent from these public input records.

## Inspected source and external obligations

The current native source was re-inspected on 22 October 2026 at checkout
`9683fe67d16aabadd31140a062082e79c7bccf43`, based on upstream
`4518846625730fabc4cd83744d4bd983a5e42b97`. The
[eight-file evidence manifest](../../../../../artifacts/setup/native-evidence.json)
records exact current hashes, spans and observations, with historical inspections
kept separately. The drift guard checks source identity; it proves no Rust refinement.

| Source | Current mechanism | Current Git blob |
| --- | --- | --- |
| [Unrolled statement](../../../../../../../full_statement_verifier/src/unrolled_proof_statement.rs) | Reads and absorbs final u32 PC/timestamps; includes boot boundary contributions in the global products. | `8b6011cc378fffde188109e0316e662dc620f762` |
| [Unified statement](../../../../../../../full_statement_verifier/src/unified_circuit_statement.rs) | Uses the corresponding typed final statement and initial/final contributions. | `6569e11b667436ec60cd93854350225b88aedb74` |
| [Contribution encoder](../../../../../../../prover/src/definitions/mod.rs) | Splits PC by mask/shift and uses distinct limb coefficients; timestamp words are field-reduced. | `5b568c4b8a7d5698bd633e3654c35fc223e9face` |
| [Challenge indices](../../../../../../../cs/src/definitions/constants.rs) | PC low/high use value coefficients 4/5; timestamps use 2/3. | `25d575306df03fa3869afa927abbc756c28e8f4a` |
| [Memory compiler](../../../../../../../cs/src/gkr_compiler/memory_like_grand_product.rs) | Retains raw PC limbs and clock tuples in PC-space read/write contributions. | `b99efc7ee516ea085c2c42399029b10fbb93f4f1` |

The earlier inspection at `0dc0a631349462700825f326516d36200be30edc` is historical.
The supplied revision `1f4a8455e9f893a1ffb3d23ad79918f243b28aca` is locally
retrievable: its unrolled-statement blob is
`8b6011cc378fffde188109e0316e662dc620f762`. The former retrieval disclaimer
was stale. Retrieval alone is not an additional audit of historical behavior.

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

Canonical closure supplies endpoint information rather than newly enforcing a
local range check. A converse requires accepted matching, the applicable initial
boot tuple, BabyBear and representable timestamp encodings; no unconditional
equivalence for arbitrary fields or initial states is claimed.
