# Whole-trace review

[Native memory soundness](History.lean) is the first v2 initialized logical-history
claim. Its short statement constructs a complete Clean online-consistent memory
history and proves that each actual imported port reads its newest preceding
write. Readonly refreshes and actual masked destination writes participate.

Review the shared [row/token data and acceptance](../Helpers/Context/Model.lean)
and [history meaning](../Helpers/Memory/History.lean). Acceptance checks the
imported native constraints, active rows and logical state/memory permutations.
The public boundary bounds only the starting machine clock and seed timestamps,
with initial four-tick alignment and one seed per address. Every per-row clock,
prior bound and newest-read conclusion is derived. Rows may be unordered.

Calculations and complete-path assembly stay under
[Proofs/Trace](../../Proofs/Trace/MemoryHistory.lean). The
[aliased-register regression](../../../Tests/InitializedHistory.lean) supplies
one native ADD row with both sources and destination at x1. Sequential readonly
refreshes are accepted. Reusing the seed for the second read satisfies local
constraints but fails logical memory matching.

[Public-image memory soundness](Initialization.lean) replaces the clock and
uniqueness premises with [public constructors](../Helpers/Memory/PublicImage.lean).
The original Sail interpreter reads every public tracked cell and the starting
architectural PC. The native initial clock is four; seed clocks are zero. Missing
registers or bytes fail construction. Seed bounds, seed clocks and unique encoded
addresses are derived, without witness-supplied initial read values.

[Public decoder recovery](Decoder.lean) constructs selected arithmetic-profile
setup rows from public bytes and original Sail decoding. Logical lookup membership
includes the native minus-one padding tail. The imported packed-mask equations
exclude that tail, recovering actual decoded public instructions and the zero flag.
Canonical decoder PC/immediate words follow in the proof layer.

[Public-image value bounds](Values.lean) derives all native reads, actual writes
and terminal word bounds from the public seed image, accepted native history and
complete decoder lookup membership. The source's decreasing-time induction is
reused; readonly ports preserve values, while native range/mask equations bound
destination writes after the zero flag is recovered. No per-row bounds are inputs.

[Actual Sail history](SailHistory.lean) realizes every accepted native transfer
from the public initial state. The [shared history representation](../Helpers/Memory/SailHistory.lean)
uses original Sail reads/writes and Clean last-write values. Native v2 mask
equations preserve x0 without NOP preprocessing; only public RAM-cell alignment
is supplied. Clock-derived [row grouping](../../Proofs/Trace/RowHistory.lean) and
[port transport](../../Proofs/Trace/PortReads.lean) recover instruction pre-state
reads and actual masked writes, including aliases. Both the aliased ADD and
[retained SUB-to-x0](../../../Tests/X0History.lean) have nonempty regressions.

[Native PC soundness](PC.lean) derives incoming PC bounds/alignment from public
indexed setup addresses, preserving RV32 truncation. The native carry/wrap
equations prove bounded successors; state matching and the public initial PC
bound the terminal PC, including empty traces. No per-row PC inputs are supplied.

[Decoded arithmetic assembly](../../Proofs/Trace/Arithmetic.lean) now derives
complete local interfaces and original Sail row retirement. The shared
[control transport](../../Proofs/Trace/Retirement.lean) preserves actual cell
reads/writes through PC preparation and retirement; no extra erased-source
readability premises are needed on v2. Concrete alias ADD and actual-byte
SUB-to-x0 regressions reach the original Sail retirement states.

[Complete arithmetic execution](Families/AddSub/Theorems.lean) now proves the
[shared reference relation](Execution.lean): actual Sail code-byte reads and
original decoding precede each normal preparation/execution/retirement step.
Native GPR metadata preserves all code bytes. Pure decoder evidence is extracted
from successful setup construction and replayed in each derived state. Native
state/memory matching derive the terminal PC and exact tracked cells, including
empty traces. The [dependent two-row regression](../../../Tests/ArithmeticExecution.lean)
stores witness rows backwards yet reaches original Sail PC 8 and x2=247.

[Word-memory public decoding](Families/WordMemory/README.md) now has a separate
native registry and short source-recovery theorem. Actual LW/SW bytes build a
complete padded logical table; native equations reject padding and recover exact
zero flags, PC/immediate bounds/alignment and original Sail source evidence,
including loads to x0. [Public ROM extraction](../Helpers/Tables/WordROMImage.lean)
now binds native ROM data to actual Sail bytes in the extracted prefix. A complete
four-MiB extraction covers the native ROM region. Initialized word-memory
[logical history](Families/WordMemory/History.lean) and
[word ranges](Families/WordMemory/Values.lean) now reuse the shared matching/clock
and decreasing-time proofs. Public seeds discharge all initial clock/value inputs;
full decoder membership supplies the zero flag. Every native port participates,
including discarded ROM-shadow reads. [Native-row assembly](Families/WordMemory/Inputs.lean)
now derives effective-address addition, bounded aligned PCs, modular successors
and native clock/port order with no per-row numerical input premises. Actual intermediate Sail reads,
boot/padding/shadow projection and instruction execution remain separate.

These are logical selected-profile results. Remaining families and physical
setup/argument fidelity remain in [the plan](../../../FORMAL_VERIFICATION_PLAN.md).
Cryptographic enforcement of the logical permutations remains a separate boundary.
Existing [local circuit claims](../Circuits/README.md) retain their explicit interfaces.
