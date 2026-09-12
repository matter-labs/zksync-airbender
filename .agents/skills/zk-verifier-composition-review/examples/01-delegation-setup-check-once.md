# Delegation setup was checked only for the first proof

## Classification

- Confirmed historical full-statement soundness bug
- Invariant: every delegation contribution is proved by the verifier-selected circuit/setup for its delegation type
- Component: unrolled full-statement delegation aggregation
- Verifier anchor: `full_statement_verifier/src/lib.rs` delegation-proof acceptance loop
- Fixed by: [`32edde7`](https://github.com/matter-labs/zksync-airbender/commit/32edde78af91101ebcb79c611c95016549895129), PR [#21](https://github.com/matter-labs/zksync-airbender/pull/21)
- Vulnerable revision: `7d80b89795ca86155290265f100c329f689ed27b`

## Composition context

CPU chunks can emit delegation requests, and separate delegation-circuit proofs satisfy those requests while contributing to shared delegation and memory accumulators. The full-statement verifier supplies the expected setup caps for every supported delegation type. Setup identity determines the circuit relation, so it must be checked for each independently supplied proof.

The outer loop had two indices with different meanings: `circuit_sequence` tracked proof position, while `delegation_type` selected the expected circuit. Neither position nor an earlier successful proof cryptographically links a later proof to the same setup.

## Intended invariant

For every delegation proof `P_i` of type `t`, before consuming any of its products:

```text
P_i.delegation_type == t
P_i.circuit_sequence == expected local convention
P_i.setup_caps == verifier_expected_setup_caps[t]
P_i.memory/delegation challenges == globally expected challenges
only then aggregate P_i's contributions
```

This is a per-proof authorization check, not a once-per-type initialization check.

## Failure

The verifier populated expected delegation setup caps internally but compared a proof's setup only when the outer `circuit_sequence == 0`. Later delegation proofs could carry a different setup cap while still reaching the same global delegation and memory accumulators.

The comment assumed that all delegation circuits of a given kind were identical regardless of the calling program. That property explains why the expected setup can be verifier-known; it does not establish that an untrusted later proof actually used it.

## Adversarial flow

1. Supply a valid first delegation proof with the expected setup so the guarded comparison passes.
2. Supply a later proof under the same declared delegation type but with attacker-chosen setup caps.
3. Have the local verifier interpret that later proof using the supplied setup wherever the proof format permits.
4. Feed its memory and delegation products into the global accumulators.
5. Reach global closure without any equality tying that proof's relation to the verifier-approved delegation circuit.

The accumulator checks only combine already accepted contribution values. They do not authenticate the circuit relation that produced each value.

## Impact and fix

The full statement could aggregate delegation contributions proved under inconsistent circuit identities. This breaks the assumption that every request was discharged by the intended precompile/delegation relation.

The fix removes the first-proof guard and compares every delegation proof's setup cap to the expected cap for its type before absorbing commitments or accumulating outputs. The PR explicitly notes that setups are populated by verification and therefore must always be checked.

Review all “check once” optimizations at composition boundaries. They are valid only if subsequent objects are cryptographically linked to the checked object by an authenticated identifier or commitment—not merely adjacent in a vector or equal by honest construction.

## Regression

- Keep the first proof valid and mutate only a non-first delegation proof's setup cap; require rejection before its contribution is consumed.
- Test several proofs of one type and interleaved proofs of several types.
- Swap setup caps between two types while retaining each declared type; require rejection.
- Instrument the outer verifier so every aggregated contribution has a preceding setup-equality event.

## Reproduction evidence

```sh
git diff 7d80b89795ca86155290265f100c329f689ed27b 32edde78af91101ebcb79c611c95016549895129 -- full_statement_verifier/src/lib.rs
```
