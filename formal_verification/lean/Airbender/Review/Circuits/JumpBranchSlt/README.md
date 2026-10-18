# Jump/branch/SLT circuit review

The current checkpoint derives native conditional-control and low-PC cleanup
effects, public original decoding and outgoing PC bounds from every imported
row equation/lookup and full padded decoder membership. Original Sail instruction
and initialized trace soundness remain open.

## Checked results

1. Read [Theorems](Theorems.lean) for the short native fixed-effects and PC-bound claims.
2. Read [Model](Model.lean) for native observables and [Decoder](Decoder.lean) for original public source construction.
3. Read [Artifact](Artifact.lean) and [control tables](Tables/Control.lean) for the
   complete v2 equations/queries and independent table meanings.

[Actual tagged table data](Tables/NativeData.lean) retains every native cleanup
and conditional row. [Certificates](../../../Proofs/JumpBranchSlt/ControlTables.lean)
prove all 65,536 cleanup rows symbolically and all 128 conditional rows by small
finite kernel checks. The v2 conditional triple keeps four flags and raw funct3
in separate key columns. [Two short shared claims](../../Helpers/Tables/Control.lean)
expose exact native tagged membership. No table equivalence is a premise.

| Observable | Native logical variable IDs |
| --- | --- |
| Initial PC / final PC | 0,1 / 13,14 |
| Initial clock / final clock | 2,3 / 15,16 |
| Packed decoder mask / destination-zero flag | 12 / 8 |
| Five selector bits | 17..21 |
| Source words / actual masked destination | 22,23 and 24,25 / 38,39 |
| Raw funct3 / conditional result | 11 / 35 |
| Cleanup key / bit one / cleaned low PC | 42 / 47 / 48 |
| Scalar-ranged candidate high PC | 43 |

[The compiled metadata audit](../../../Proofs/JumpBranchSlt/ArtifactChecks.lean)
checks all 36 equations/16 lookups, three register ports, native clocks, ten-column
decoder query and the 16-column setup layout. Generic cleanup/conditional regions
start at 0/65536 with tags 17/43; no dummy row is inserted. [Query assembly](../../../Proofs/JumpBranchSlt/Queries.lean)
extracts both actual native queries and derives all fields of the local claim.

[Regressions](../../../../Tests/JumpControl.lean) include a full active native JAL
x1,+8 witness, signed/unsigned and equality cases, changed-result/out-of-domain
rejection and the actual JAL alignment equation. A cleanup row with bit one set
is valid table data; the native jump constraint rejects that target. Explicit
import targets reject missing/mismatched fixed-table profiles.

[PC calculations](../../../Proofs/JumpBranchSlt/PC.lean) derive both outgoing limb
bounds under explicit supported masks 1/2/4/8/16, selecting JAL, JALR,
SLT/SLTU, SLTI/SLTIU and conditional branches respectively. Native Boolean/packed
equations supply exclusivity; high PC equals ranged variable 43 and low PC is the ranged
raw or cleaned key. No outgoing/terminal range or verifier closure is supplied.
[The JAL -4 regression](../../../../Tests/JumpPC.lean) accepts canonical target
0xfffffffc. Its field-minus-one high variant passes all polynomials and every
other native query, but fails actual scalar query index 5. The source F01 witness
shape is excluded locally; no source closure interface is adopted.

[Public control decoding](Decoder.lean) now derives the supported mask from
actual bytes and original Sail decoding through the reused sparse constructor.
[Calculations](../../../Proofs/JumpBranchSlt/Decoder.lean) reject every hole/tail
sentinel using native packed-mask bounds, then recover canonical PC/immediate
words, incoming alignment, raw funct3 and the exact zero flag. The short public
claim adds no mask, word-range or expected decoding-result premise.

[The native v2 decoder](../../../../../../cs/src/machine/ops/unrolled/decoder/jump_slt_branch.rs)
retains original SLT/SLTI and jumps to x0; SLTI uses mask 8 and branches mask
16. JAL also retains raw opcode funct3, so the [actual JAL -4 byte fixture](../../../../Tests/JumpDecoder.lean)
uses tag 7. That full native row passes; the earlier local tag-zero row is excluded
by public membership. The malformed high-PC variant still has public membership
and satisfies all polynomials, but the native range query rejects it. The fixture
retains UNIMP at PC 4 and original SLTIU-to-x0 at PC 8; full padding, all branch
conditions and missing byte/capacity checks pass.

Actual native program-prefix export, initialized reads, original Sail clauses/
retirement, full family execution and terminal matching remain open. General Rust/JSON/Lean refinement,
physical setup/normalization/LDE and cryptographic argument enforcement remain
separate. No implementation vulnerability is established.
