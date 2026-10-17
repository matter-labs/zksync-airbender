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

This is a logical initialized-memory result. Public Sail image binding, operand
bounds, preprocessing, public decoding and a whole Sail execution reaching the
native terminal PC/cells remain in [the plan](../../../FORMAL_VERIFICATION_PLAN.md).
Cryptographic enforcement of the logical permutations remains a separate boundary.
Existing [local circuit claims](../Circuits/README.md) retain their explicit interfaces.
