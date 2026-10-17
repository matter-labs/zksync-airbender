# ADD/SUB circuit review

This directory models ADD, ADDI, SUB, LUI and AUIPC as actual destination-write
and architectural PC transitions using the original upstream Sail clauses.

## Checked results

1. Read [Theorems](Theorems.lean) for generic signed-equation and native Mersenne31 soundness.
2. Read [Model](Model.lean) for the constraint relation, observable mappings and local interfaces.
3. Read [Reference](Reference.lean) and [Artifact](Artifact.lean) for selected semantics and native input.

The public surface has two theorem statements: `Airbender.AddSub.soundness` and
`Airbender.AddSub.mersenne31_soundness`. Selector recovery, arithmetic
and PC calculations stay under Proofs. Individual selector bits and result/PC
bounds are derived; packed native decoding, preprocessing, input bounds and
original Sail reads remain explicit until initialized history is backported.
The final PC is modular RV32, including aligned wraparound at 0xfffffffc.
Native [clock and port descriptors](Artifact.lean) now come from typed v2 JSON;
[clock effects](../../../Proofs/AddSub/Timestamp.lean) derive four-tick advancement
and strict port order under the shared [clock inputs](../../Helpers/Context/README.md).

| Observable | Native logical variable IDs |
| --- | --- |
| Initial PC / final PC | 0,1 / 13,14 |
| Packed decoder mask / destination-zero flag | 12 / 8 |
| Source words / immediate | 25,26 and 27,28 / 9,10 |
| Actual destination write | 37,38 |
| Raw arithmetic result / low and high carries | 29,30 / 43 and 33 |

[Accepted native execution and rejected changed write](../../../../Tests/AddSub.lean)
and [native PC wraparound](../../../../Tests/PC.lean) exercise the artifact proof.
See [trust boundaries](../../../../TRUST_AND_REVIEW.md) before extending the claim.
