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

These are logical selected-profile results. Subsequent Sail read transport,
preprocessing/row assembly and whole Sail execution reaching the native terminal
PC/cells remain in [the plan](../../../FORMAL_VERIFICATION_PLAN.md).
Cryptographic enforcement of the logical permutations remains a separate boundary.
Existing [local circuit claims](../Circuits/README.md) retain their explicit interfaces.
