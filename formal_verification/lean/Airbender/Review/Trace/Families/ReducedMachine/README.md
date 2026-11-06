# Actual native reduced trace review

Start with the [regenerated-artifact registry](../../../Helpers/Context/ReducedMachine.lean)
and [short public history claims](History.lean). They use the actual monolithic
117-equation v2 artifact, not the historical shipped JSON or a table-equivalence
premise. The four-field modeled setup table stays explicit.

[Native clock extraction](../../../../Proofs/ReducedMachine/NativeTimestamp.lean)
checks actual Boolean rows27..30, final-clock equations115/116 and all eight
native timestamp queries8..15. [Metadata](../../../../Proofs/ReducedMachine/NativeClockMetadata.lean)
retains the actual three previous-clock pairs, borrow bits and offsets0/1/2.
[Proof assembly](../../../../Proofs/Trace/Families/ReducedMachine/History.lean)
instantiates the unchanged shared clock/history machinery. Public Sail seed/PC
construction and accepted native logical matching derive all local/prior clocks,
strict access order, terminal four-tick row count, complete Clean memory
consistency and newest preceding reads for each native port. Readonly refreshes
and actual mixed addresses/masked writes stay in the relation. Row list order
need not be chronological. No expected read, per-row clock/order or supplied
intermediate-state answer is used.

[Four conditional regressions](../../../../../Tests/NativeReducedHistory.lean)
cover low-clock carry, finite clock-epoch overflow, nonpreceding reads and wrong
terminal row counts. They are not full positive native execution fixtures.

This establishes logical initialized clock/memory history. Word ranges still
need decoded native write preservation and shared range induction; memory
consistency alone does not prove all source limbs bounded. Original public
instruction decoding, canonical source keys, complete word/PC effects and Sail
execution remain open, as do workers/accounting/protocol/padding/terminal/init
and physical enforcement boundaries. Terminal clock counting is not terminal
machine-state soundness. See [current status](../../../../../VERIFICATION_STATUS.md)
and [trust boundaries](../../../../../TRUST_AND_REVIEW.md).
