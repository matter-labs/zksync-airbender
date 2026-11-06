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

## Original public shift decoding

[The short public decoder claim](Decoder.lean) now recovers the original public
instruction entry and actual native mask/source/rd/x0/immediate/funct3 fields.
[Complete sparse/padded membership](../../../Helpers/Decoder/ReducedMachine.lean)
is checked at the imported native query; original public bytes and stateful Sail
decoding construct its independent table. [Native packing](../../../../Proofs/ReducedMachine/NativeShiftDecoder.lean)
excludes holes/tail, and [trace assembly](../../../../Proofs/Trace/Families/ReducedMachine/Decoder.lean)
keeps calculations under Proofs. The current profile includes only original
SLL/SRL/SRA/register/immediate forms. [Eight regressions](../../../../../Tests/NativeReducedDecoder.lean)
retain all twelve ordinary/x0 forms and reuse only original byte/decode lemmas,
not a split-family native table. This does not establish native Rust preprocessing
exports, universal fixed-ROM binding, other combined operations or a full accepted
execution fixture. Native write preservation, initialized source ranges and
complete instruction/execution effects remain next.

## Initialized word ranges and native source keys

[Concrete fixedData](FixedData.lean) selects the actual native pool while retaining
rows and explicit state/memory boundaries. It assumes no equivalence with another
table. [Native preservation](../../../../Proofs/ReducedMachine/NativeShiftPreservation.lean)
proves readonly refreshes and the actual masked destination write preserve ranges
from earlier reads, using original decoded rd/x0 fields. [Shared range induction](../../../../Proofs/Trace/Families/ReducedMachine/Values.lean)
then derives all native read/write/terminal word bounds from public seeds and
accepted matching; the [public interface](Values.lean) has no per-row range or
preservation-rule premise. [Both source keys](Sources.lean) are now exact natural
limb/amount/direction packings using the derived low source bound. Calculation
proofs stay under Proofs, including all32amounts and the arithmetic zero-shift
exception. [Nine regressions](../../../../../Tests/NativeReducedRanges.lean)
retain shift/sign boundaries, reject oversized actual reads/writes and preserve
bounded x0 source participation. No complete positive117-equation execution
fixture is asserted. Other combined profiles, original Sail GPR/cell/word effects,
numerical PC and preprocessing/physical/protocol/terminal/init remain separate.
