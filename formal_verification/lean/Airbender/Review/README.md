# Review guide

This directory states claims, observables and assumptions. Calculations live in
Proofs; artifact interpretation has a separate Import boundary.

## Main checked results

| Result | Where to review it |
| --- | --- |
| Conditional v2 arithmetic rows agree with original Sail destination/register and PC effects. | [ADD/SUB](Circuits/AddSub/README.md) |
| Initialized logical v2 memory matching constructs complete Clean history and newest preceding reads. | [Trace history](Trace/README.md) |
| Public Sail image construction supplies actual seed values and initial PC, rejecting missing registers/bytes. | [Initialization](Trace/Initialization.lean) |
| Public arithmetic-profile decoding and full padded lookup recover actual Sail instructions; initialized history derives native word bounds. | [Decoder](Trace/Decoder.lean), [values](Trace/Values.lean) |
| Complete initialized arithmetic execution reaches exact terminal PC/cells through original Sail normal steps. | [Arithmetic execution](Trace/Families/AddSub/Theorems.lean) |
| Initialized word-memory execution checks actual fetched/decoded original LW/SW and exact terminal PC/architectural cells, retaining full native shadow matching. | [Word-memory execution](Trace/Families/WordMemory/Theorems.lean) |
| Fixed native zero boot derives original execution; explicit Sail padding derives full ROM coverage while complete native paths preserve independent zero shadows. | [Native boot](Trace/Families/WordMemory/NativeBoot.lean) |

Start with [Properties](Helpers/Properties.lean) for `Properties.Soundness` and
`Properties.Completeness`, then choose
[one circuit](Circuits/README.md) or [whole-trace review](Trace/README.md).
The trace route connects checked native history to complete selected arithmetic
and word-memory Sail execution; other families and physical argument enforcement
remain separate.

## Scope and evidence

[Verification status](../../VERIFICATION_STATUS.md) lists actual v2 coverage.
[Trust boundaries](../../TRUST_AND_REVIEW.md) records what hashes, parsing,
local interfaces and original reference selection establish.
Every source-declared public theorem in Review must have an explicit axiom root.
