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
original Sail reads remain explicit until public decoding and history transport
discharge them for initialized execution.
The final PC is modular RV32, including aligned wraparound at 0xfffffffc.
V2 retains the original opcode mask and operands for x0 writes. The
[nonzero-operand SUB-to-x0 regression](../../../../Tests/CircuitRows.lean) applies
the public theorem to original Sail execution while the actual write is zero.
Native [clock, port and decoder descriptors](Artifact.lean) now come from typed v2 JSON;
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

[Setup metadata](../../Helpers/Tables/SetupColumns.lean) now checks this artifact's
12 physical columns, scalar groups at 0/1, ten-wide decoder group at 2, native
capacity and reserved final row. No generic lookup groups are silently added;
all 62 table offsets are zero. The existing local/trace claims are unchanged;
actual Rust setup exports and argument enforcement remain separate.

[Shared native scalar prefixes](../../Helpers/Tables/NativeScalars.lean) now bind
the complete range16/timestamp19 data and modeled active zero fill to the existing
Clean range meanings. Both compiled columns 0/1 are checked. Physical trace/
normalization/LDE/argument refinement stays open.

[Actual native arithmetic decoder data](Tables/NativeSetupData.lean) now has a
[complete row certificate](../../../Proofs/AddSub/NativeSetup.lean) from independent
public bytes and original Sail decoding. The [short source claim](../../Trace/Families/AddSub/NativeDecoder.lean)
uses native equations and actual exported membership. Signed ADDI, original x0
SUB, raw U-type funct3 and a full native ADD row at PC 24 after an UNIMP hole are
checked. This certificate covers its concrete public input; general decoder
refinement and custom MOP semantics remain open.

[Sparse initialized execution](../../Trace/Families/AddSub/SparseExecution.lean)
now reuses these arithmetic calculations and original Sail clauses through the
same native history/retirement/terminal assembly as the strict claim. Actual
public construction and complete native matching derive internal source/PC
facts. [The full post-hole alias regression](../../../../Tests/SparseArithmeticExecution.lean)
selects actual exported PC 24 and derives PC 28 and x1=246, with the public UNIMP
hole intact. Physical trace/argument refinement remains separate.
