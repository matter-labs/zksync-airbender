# Review guide

This directory states claims, observables and assumptions. Calculations live in
Proofs; artifact interpretation has a separate Import boundary.

## Main checked results

| Result | Where to review it |
| --- | --- |
| Conditional v2 arithmetic rows agree with original Sail destination/register and PC effects. | [ADD/SUB](Circuits/AddSub/README.md) |

Start with [Properties](Helpers/Properties.lean) for `Properties.Soundness` and
`Properties.Completeness`, then choose
[one circuit](Circuits/README.md) or [whole-trace review](Trace/README.md).
The latter currently records pending integration rather than a v2 execution theorem.

## Scope and evidence

[Verification status](../../VERIFICATION_STATUS.md) lists actual v2 coverage.
[Trust boundaries](../../TRUST_AND_REVIEW.md) records what hashes, parsing,
local interfaces and original reference selection establish.
Every source-declared public theorem in Review must have an explicit axiom root.
