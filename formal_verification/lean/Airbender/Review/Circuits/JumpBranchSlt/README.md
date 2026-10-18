# Jump/branch/SLT circuit review

The current checkpoint derives native conditional-control and low-PC cleanup
effects from every imported row equation and lookup. Original Sail instruction
and initialized trace soundness remain open.

## Checked results

1. Read [Theorems](Theorems.lean) for the short native fixed-effects claim.
2. Read [Model](Model.lean) for exact native observables and derived values/bounds.
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

Public decoding, initialized reads, original Sail clauses/retirement and full
family execution remain open. Retest native outgoing/terminal PC behavior before
adopting a source finding or closure interface. General Rust/JSON/Lean refinement,
physical setup/normalization/LDE and cryptographic argument enforcement remain
separate. No implementation vulnerability is established.
