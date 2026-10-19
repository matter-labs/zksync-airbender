# Unsigned MUL/DIV trace review

## Public claims

Start with [the numerical theorem](Theorems.lean), then [history](History.lean)
and [word bounds](Values.lean). Actual public seed/PC reads, stateful original
Sail decoding and full native matching derive every local numerical interface.
The conclusion retains original public source evidence, actual query equality,
selected operation results and actual masked destination writes. No per-row
read, range, selector, zero flag or desired result is supplied.

## Native and reference connections

[The circuit guide](../../../Circuits/MulDiv/README.md) identifies all native
constraints, numerical calculations and actual port/write words.
[Stateful setup](../../../Helpers/Decoder/StatefulSetup.lean) preserves native
4*i locations, unsupported holes and every sentinel tail row. Original decoding
reads the public misa configuration. Missing bytes and decoding errors reject;
the unchanged source frame proof supplies state preservation and misa replay.
Full native mask equations exclude sentinel queries before source recovery.
[Internal assembly](../../../../Proofs/Trace/Families/MulDiv/Results.lean)
combines unchanged shared initialized range/history induction with the checked
four-operation numerical theorem.

## Regressions and remaining boundaries

[Sixteen complete initialized traces](../../../../../Tests/MulDivInitializedFixture.lean)
cover four operations, both actual write modes and ordinary/zero divisors.
[Original decoder checks](../../../../../Tests/MulDivDecoderCases.lean) retain
all x0 opcodes and reject disabled M. [Argument boundary checks](../../../../../Tests/MulDivMetadata.lean)
reject locally valid wrong tags and a compensating flag-2/unbounded write using
actual public membership. Capacity, unsupported signed forms, UNIMP holes and
the full tail are checked. No implementation defect is established.

Original Sail operation clauses, preparation/retirement and finite fetched
execution remain unfinished. Native physical initialization, general
Rust/JSON/compiler refinement, cryptographic enforcement, unified execution,
protocol composition and completeness remain separately scoped. Follow
[the plan](../../../../../FORMAL_VERIFICATION_PLAN.md).
