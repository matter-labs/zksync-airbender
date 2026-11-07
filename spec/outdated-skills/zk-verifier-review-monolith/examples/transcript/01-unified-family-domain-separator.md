# Unified prover and verifier disagreed on the family separator

## Classification

- Confirmed historical same-instance Fiat-Shamir parity/completeness bug
- Component: unified full-statement external-challenge transcript
- Verifier anchor: `full_statement_verifier/src/unified_circuit_statement.rs` challenge derivation
- Direct consequence: the provided prover and verifier derived different
  memory/delegation challenges for honest unified proofs
- Additional security purpose: branch-specific domain separation for the
  universal unrolled/unified dispatcher introduced by the same fix
- Fixed by: [`7bfd63b`](https://github.com/matter-labs/zksync-airbender/commit/7bfd63b42fc56b5b44c0c24200e930259d4eb95b)
- Vulnerable revision: `745cfa076989dbd1e430c422be9803c2bdb8c2d2`

## Failure

The unified prover used the shared unrolled-family transform. For each nonempty
family, that transform absorbed a padded family identifier before the family's
memory caps. The unified main family was therefore represented as:

```text
pad16(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX) || unified memory caps
```

The matching full-statement verifier read `num_circuits > 0` and immediately
entered the proof loop. It absorbed each returned memory cap, but never absorbed
`REDUCED_MACHINE_CIRCUIT_FAMILY_IDX` first:

```text
prover:   public state || family tag || cap_0 || cap_1 || ...
verifier: public state ||               cap_0 || cap_1 || ...
```

The later external-challenge equality check could not repair this mismatch:
the two sides had already finalized different Blake2s inputs and therefore
derived different challenges except with a hash collision. The directly
established historical failure was honest-proof rejection.

## Universal-dispatch qualification

Before this commit, the `unified_reduced_machine` verifier workload directly
called the unified recursion verifier. If the recursion chain authenticated that
single-mode binary/setup, its program identity could already bind the verifier
mode externally; the diff alone does not establish a pre-fix cross-family replay
through that binary.

Commit `7bfd63b` simultaneously changed the workload to a universal dispatcher
that reads a prover-supplied `op_type` and selects the unrolled or unified
recursion verifier. One binary hash authenticates the dispatcher code but does
not by itself identify its runtime branch. The family tags used by the two
branches then provide branch-specific transcript framing. A concrete replay
still depends on compatible proof layouts, setup checks, and accepted relations;
do not claim unconditional portability between families.

## Required invariant

For a same-instance prover and verifier, the complete pre-challenge transcript
must match exactly:

```text
seed_0 = H(public statement and final-state prefix)
seed_1 = H(seed_0 || pad16(REDUCED_MACHINE_CIRCUIT_FAMILY_IDX))
seed_2 = H(seed_1 || first unified memory cap)
...
```

More generally, a verifier-selected mode must be bound either by the transcript
or by authenticated enclosing context that uniquely determines it. A
single-mode authenticated binary may close that obligation; a prover-selected
branch in one multi-mode binary does not do so merely because the dispatcher is
hashed.

## Impact and fix

The fix absorbs the padded unified-family identifier once, immediately after
checking that the main proof count is positive and before the first proof/cap.

Regression coverage should:

- compare prover and verifier transcript events and seeds at the family marker
  and after every cap;
- assert the tag occurs exactly once before the first dependent challenge;
- cover one and multiple unified chunks plus empty/nonempty delegation groups;
- for a universal binary, change only the selected operation and require either
  a different authenticated statement context or a different transcript prefix;
  and
- distinguish an honest parity failure from conditional cross-mode replay in
  the reported impact.

## Reproduction evidence

```sh
git diff 745cfa076989dbd1e430c422be9803c2bdb8c2d2 7bfd63b42fc56b5b44c0c24200e930259d4eb95b -- full_statement_verifier/src/unified_circuit_statement.rs tools/verifier/src/main.rs
```
