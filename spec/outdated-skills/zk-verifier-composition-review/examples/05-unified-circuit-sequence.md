# Unified circuit sequence used a dead legacy field

## Classification

- Confirmed historical multi-chunk verification bug
- Invariant: verifier chunk-order and coverage checks rely only on live, constrained protocol state
- Component: unified full-statement verifier
- Verifier anchor: `full_statement_verifier/src/unified_circuit_statement.rs` multi-chunk output checks
- Security character: honest multi-chunk rejection; removing the stale check does not itself prove reorder safety
- Fixed by: [`85c4925`](https://github.com/matter-labs/zksync-airbender/commit/85c492522717063abc7191f8fb603ca728412e55)
- Vulnerable revision: `728c6a2edc7d2e271b77627d5a9a5361e09c30de`

## Composition context

Older unrolled proof formats exposed a `circuit_sequence` value that the outer verifier could compare with its loop index. The unified format retained the field for structural compatibility but no longer used it as a sequence number; valid unified proofs emitted zero.

Execution order in the unified design is instead carried by live algebraic relations: shared RAM/machine-state products, PC/timestamp boundaries, and whatever participant-count or transcript ordering the outer statement enforces. A dead output field provides neither soundness nor useful redundancy.

## Intended invariant

For the historical unified format:

```text
proof_output.circuit_sequence == 0        # fixed legacy-format value
```

Separately, the audit must establish:

```text
every supplied chunk is verified
every required chunk is present exactly once
PC/timestamp and RAM/state contributions close globally
reordering cannot alter the accepted execution statement
```

These are different claims and must not be conflated.

## Failure

The full-statement verifier required `current.circuit_sequence == circuit_sequence`, where the right-hand side was the outer loop index. The second and every later honest unified proof therefore failed even though the format correctly left its legacy field at zero.

The check looked like defense-in-depth, but it asserted semantics that the producer and circuit no longer supplied. Worse, its presence could give reviewers false confidence that chunk order was authenticated when the field was neither live nor constrained for that purpose.

## Failure flow

1. Produce a valid execution requiring at least two unified chunks.
2. The first output has `circuit_sequence = 0` and passes the loop-index check.
3. The second valid output also has the format-mandated value zero.
4. The outer loop expects one and rejects before global composition can complete.

This is a completeness failure, not a demonstrated soundness bypass. The security task created by the fix is to verify that live global relations—not this field—establish the intended whole-execution semantics.

## Impact and fix

All honest unified campaigns with more than one chunk were unverifiable. The fix changes the assertion to the actual format invariant, `current.circuit_sequence == 0`, and documents the field as unused legacy state.

When removing or downgrading a sequence field, construct a chunk-coverage proof: identify the authoritative ordering mechanism, its endpoints, monotonicity/continuity checks, duplicate prevention, and final closure. A passing multi-chunk test alone does not prove those properties.

## Regression

- Verify two, three, and many unified chunks whose legacy sequence field is zero.
- Mutate the field to nonzero and require rejection as malformed output.
- Swap two chunks, duplicate one, and omit one; require either rejection or demonstrate why order is algebraically irrelevant while coverage still closes.
- Trace PC/timestamp and RAM/state contributions across the same mutations to show which live invariant detects them.

## Reproduction evidence

```sh
git diff 728c6a2edc7d2e271b77627d5a9a5361e09c30de 85c492522717063abc7191f8fb603ca728412e55 -- full_statement_verifier/src/unified_circuit_statement.rs
```
