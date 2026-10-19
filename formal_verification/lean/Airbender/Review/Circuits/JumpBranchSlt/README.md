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

Actual native program-prefix export and initialized native history are certified below. Original Sail cell reads, clauses/
retirement, full family execution and terminal matching remain open. General Rust/JSON/Lean refinement,
physical setup/normalization/LDE and cryptographic argument enforcement remain
separate. No implementation vulnerability is established.

## Actual exported decoder

[The native prefix](../../../../artifacts/setup/jump-decoder-native.json) is imported
as [literal public data](Tables/NativeSetupData.lean). It uses the same three-word
public fixture and independently calls the pinned signed Rust decoder. [Certificates](../../../Proofs/JumpBranchSlt/NativeSetup.lean)
reuse the arithmetic proof structure to check every actual prefix/tail row against
original Sail construction. The short exported-decoder claim in [Theorems](Theorems.lean)
derives original source evidence and PC bounds from full native constraints and
actual exported membership. No table-equivalence or range premise is supplied.

[Regressions](../../../../Tests/NativeJumpSetup.lean) retain raw JAL tag 7, the
UNIMP hole, original SLTIU-to-x0 at PC 8 and all million padded slots. The full
accepted JAL row applies the claim; the local tag-zero query is rejected. Public
text equality and crossed arithmetic/control importer rejection are checked.
General Rust decoder/physical trace refinement and initialized execution remain open.

## Initialized native history

[The separate registry](../../Helpers/Context/JumpBranchSlt.lean) binds every
imported control port and clock column. [Calculations](../../../Proofs/JumpBranchSlt/Timestamp.lean)
prove native four-tick/port-order laws, including lower-clock carry. [The short
history claim](../../Trace/Families/JumpBranchSlt/History.lean) uses actual public
Sail seed/PC reads and complete native matching to derive all row/prior clocks,
complete Clean history and newest reads. [The JAL fixture](../../../../Tests/ControlHistory.lean)
keeps both readonly x0 refreshes and the actual link write; stale local reads fail
matching. [Initialized word bounds](../../Trace/Families/JumpBranchSlt/Values.lean)
and [Sail cell transfers](../../Trace/Families/JumpBranchSlt/SailHistory.lean) now
reuse actual decoded masks and shared history induction, including x0 writes.
Original instruction execution and terminal instruction-state matching remain open. No expected read, schedule or per-row clock is supplied.

[Initialized decoded register transfers](../../Trace/Families/JumpBranchSlt/Registers.lean)
now connect original Sail GPR accessors to actual native source/destination ports.
All three reads use a constructed cell-history pre-state, including aliases, and
the final port performs the actual masked write. Original control operation
semantics, instruction clauses and PC retirement remain separate.

## Saved jump links

[The native link claim](Theorems.lean) now derives the actual JAL/JALR PC+4 write,
including discarded x0, from public sparse construction, full lookup membership
and every native constraint. Jump masks classify the operation domain; actual
packed-mask equations recover selectors. [Calculations](../../../Proofs/JumpBranchSlt/Link.lean)
reuse original carry extraction and shared modular addition with v2 equation/column
bindings. [Tests](../../../../Tests/JumpLink.lean) check public JAL/JALR/x0 links,
all native constraints for local RV32 wrap, and altered-write rejection. The wrap
case is not an initialized/public-decoder trace, and the new logical JALR/x0
words have no new native export certificate. Target calculation is checked below;
original Sail clauses/PC retirement remain open.

## Initialized jump targets

[Native calculations](../../../Proofs/JumpBranchSlt/Target.lean) reuse modular
addition and bit cleanup with actual target/carry bindings. Candidate high scalar
query five derives its bound; no v3 final-high closure interface is copied.
[The short trace claim](../../Trace/Families/JumpBranchSlt/Targets.lean) derives
source bounds from initialized matching and PC/immediate bounds, jump identity
and JAL parity from original public decoding. JALR clears bit zero; the native
bit-one assertion enforces four-byte alignment. [Tests](../../../../Tests/JumpTarget.lean)
check exported negative JAL, initialized aliasing JALR with public source 257,
local x0/wrap targets and rejected bit-one targets despite valid cleanup. Full
original instruction clauses/retirement and terminal instruction-state matching
remain separate; local wrap and logical-fixture export boundaries stay explicit.

## Initialized comparison results

[Native calculations](../../../Proofs/JumpBranchSlt/Comparison.lean) preserve
positive flags 31/33 and derive their complements from actual high-limb shifts
and scalar queries. Original subtraction/borrow lifting and unchanged signed
word ordering feed the real conditional table and actual masked writes.
[The short initialized claim](../../Trace/Families/JumpBranchSlt/Comparisons.lean)
derives ranges from full matching and selectors/signedness/x0 from original
public decoding. [Tests](../../../../Tests/ControlComparisons.lean) check all
four comparisons with separately initialized states, signed/unsigned disagreement,
negative immediate, discarded raw one and rejected sign-shift range violation.
Branch semantics and original Sail instruction/PC execution remain separate.
