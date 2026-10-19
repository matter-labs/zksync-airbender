# Family execution review

The selected v2 arithmetic family has a short [execution theorem](AddSub/Theorems.lean)
and [original Sail step/trace aliases](AddSub/Execution.lean). The shared
[reference relation](../Execution.lean) requires actual code-byte reads, original
decoding, matching architectural PC and normal Sail preparation/execution/retirement.
Its terminal relation observes exact native PC and tracked register/RAM words.

Public inputs construct the initial image and selected setup. Native acceptance
and complete logical decoder membership derive row order, intermediate states,
operands, ranges, selectors, preprocessing and retirement. Only public RAM-cell
alignment is supplied. Calculations stay in [Proofs](../../../Proofs/Trace/Composition.lean).
Other families and physical/cryptographic argument enforcement remain pending.

[The complete-row arithmetic bridge](AddSub/PhysicalSetup.lean) now consumes
actual decoder columns of the source-shaped active setup model. Its initialized
alias regression derives original Sail PC 28/x1=246 through complete native
matching. Setup projections, rather than table-equivalence premises, connect
physical columns to existing lookup meanings. Rust/normalization/LDE and
cryptographic enforcement remain separate.

[The control family prerequisite](../../Circuits/JumpBranchSlt/README.md) now
imports all native equations/queries and proves actual fixed-table effects on a
nonempty active JAL witness. Its public decoding, initialized original Sail
execution and terminal-PC/closure assessment remain open; it has no family
execution claim yet.

## Unsigned MUL/DIV

[The family guide](MulDiv/README.md) covers initialized native history and numerical results for four unsigned operations. It retains stateful original decoding and actual x0 writes; operation clauses, retirement and fetched execution remain separate.
