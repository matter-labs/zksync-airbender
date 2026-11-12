# Batched Sumcheck used the wrong last-round convention

## Classification

- Producer-parity history: confirmed historical Sumcheck implementation regression
- Component: batched GKR round evaluation and terminal interpolation
- Claim-chain location: final round polynomial → folded input evaluations → terminal gate pin
- Security character: honest-proof rejection from mixing two valid but incompatible encodings
- Fixed by: [`42e910a`](https://github.com/matter-labs/zksync-airbender/commit/42e910ad2e3ee507706ae8a2e8290a6bd540b55a)
- Vulnerable revision: `ad95db69bdfb98ce3e511bdf3c5948cde931da6d`

## Protocol context

The final Sumcheck round is both a polynomial round and the handoff to direct gate evaluation. An implementation may either materialize an explicit last-round polynomial inside the evaluation loop or retain the ordinary quadratic-only representation, collect the two final source values, and interpolate after the loop.

Both conventions can be correct. They are not byte- or slot-compatible: `EXPLICIT_FORM` changes what accumulator entries mean, which source evaluations are recorded, and where final interpolation occurs.

## Intended claim relation

Under the restored convention:

```text
all rounds, including the last, use the ordinary quadratic-only accumulator layout
on the last round, record the final two evaluations of every referenced source
after the loop, interpolate/evaluate using the shared last-round formula
assert resulting claim == direct batched gate evaluation at the full random point
```

There must be exactly one owner of terminal interpolation.

## Failure

A merge retained a dedicated last-round match arm from one implementation inside a loop structured according to another implementation. The arm set `EXPLICIT_FORM = true` and wrote full second-point evaluations into an accumulator slot whose consumers expected quadratic-only stratification with interpolation deferred outside the loop.

The final coefficient vector was therefore internally well-typed but semantically mixed: producer and consumer assigned different meanings to the same slots. The bug was caught by the final-claim self-check rather than a memory or parsing error.

## Failure flow

1. Reach the final round of a batched Sumcheck with a nontrivial quadratic relation.
2. Evaluate it using the special explicit-form arm.
3. Store values in the explicit convention's accumulator layout.
4. Continue through surrounding code that applies the deferred quadratic-only interpolation convention.
5. Derive a terminal claim different from direct evaluation of the folded gate.
6. Reject an honest proof at the final pin.

This historical regression is a completeness bug. A verifier independently evaluating the gate correctly does not accept the bad claim. The audit lesson is that a last-round shortcut is a protocol variant even when no serialized field changes type.

## Impact and fix

The Sumcheck chain no longer terminated at the actual gate relation. The fix deletes the dedicated explicit-form arm, uses the ordinary `3..` path for all later rounds, and conditionally records final source evaluations when `round + 1 == total_sumcheck_rounds` for one deferred interpolation.

When reviewing a shortcut, trace sender layout, parser layout, round identity, recorded source values, interpolation owner, and final gate formula as one unit.

## Regression

- Differential-test against a naive prover for linear, quadratic, mixed base/extension, and zero-quadratic gates.
- Exercise the minimum legal round count and several longer instances.
- Compare the final coefficient vector, final source evaluations, folded claim, and direct gate evaluation.
- Assert terminal interpolation executes exactly once.
- Run with self-checks in the same feature/configuration used by production generation.

## Reproduction evidence

```sh
git diff ad95db69bdfb98ce3e511bdf3c5948cde931da6d 42e910ad2e3ee507706ae8a2e8290a6bd540b55a -- prover/src/gkr/prover/sumcheck_loop/batch_evaluation.rs
```
