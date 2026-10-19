# Unsigned MUL/DIV trace review

## Public claims

Start with [complete fetched execution](FetchedExecution.lean), then [the numerical theorem](Theorems.lean), [history](History.lean)
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

Complete finite fetched Sail execution is now checked in the latest checkpoint below. Native physical initialization, general
Rust/JSON/compiler refinement, cryptographic enforcement, unified execution,
protocol composition and completeness remain separately scoped. Follow
[the plan](../../../../../FORMAL_VERIFICATION_PLAN.md).

## Original Sail register transfers

[Register history](Registers.lean) derives actual original Sail operand/old-destination reads, masked writes, code/misa preservation and all segment states. [The observable definitions](../../../Helpers/Memory/MulDiv.lean) keep the statement short. The original generic three-port lemmas are copied unchanged; native x0 preservation uses actual v2 equations. [Sixteen initialized cases](../../../../../Tests/MulDivRegisters.lean) check actual writes/full-state x0 stuttering. [A two-MUL alias sequence](../../../../../Tests/MulDivRegisterChain.lean) derives second-row reads 123/7, write 861 and original decoding after a real prefix update. Stale old-destination timestamps pass local equations/decoding/state matching but fail native memory matching. Original local operation/PC execution is covered by the later checkpoint below; general refinement remains separate.

## Original local instruction execution

Start with [the instruction-history theorem](Execution.lean) and [its observables](../../../Helpers/Memory/MulDivExecution.lean). They combine real constructed segment states with original MUL/MULHU/DIVU/REMU clauses and actual nextPC preparation/PC retirement. [All sixteen initialized cases](../../../../../Tests/MulDivExecution.lean) and [the actual alias sequence](../../../../../Tests/MulDivRegisterChain.lean) apply the claim; [a full imported native row](../../../../../Tests/MulDivPC.lean) checks RV32 PC wrap. Complete fetched execution still needs stateful decoder composition and native row boundaries; physical initialization, cryptographic enforcement and general compiler refinement remain separate.

## Complete original fetched execution

Start with [the public execution theorem](FetchedExecution.lean), which uses the unchanged shared complete-execution observations. [Internal family assembly](../../../../Proofs/Trace/Families/MulDiv/Composition.lean) derives actual public fetch/stateful decoding, native PC row boundaries and every original clause/retirement step. [Stateful composition](../../../../Proofs/Trace/StatefulComposition.lean) uses actual misa preservation and the unchanged decoder-frame proof instead of supplying replay or purity. [Complete regressions](../../../../../Tests/MulDivFetched.lean) cover all sixteen cases and their arithmetic terminal reads, the reversed alias program reaching PC eight/x1=x3=861 and empty rows. Physical initialization, compiler/cryptographic refinement, unified/protocol execution and completeness remain separate.
