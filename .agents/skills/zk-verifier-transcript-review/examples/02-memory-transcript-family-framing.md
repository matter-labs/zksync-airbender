# Memory transcript omitted family and delegation framing

## Classification

- Confirmed historical cross-proof transcript-coverage bug
- Component: unrolled memory/delegation Fiat-Shamir transform
- Fixed by: [`386ab26`](https://github.com/matter-labs/zksync-airbender/commit/386ab2621f484cd8d923acbbf3e00467c8bd46ae)
- Vulnerable revision: `6be5025cc072e7ae503726a77d4cc0be1fd59577`

## Failure

Memory caps were absorbed without the complete framing later added by the fix: final register values/timestamps, final PC, circuit-family identifiers, the inits/teardowns family tag, and delegation types in sorted order.

## Impact and fix

The same cap sequence could have different semantic owners while producing the same challenge seed, weakening binding between global memory products and their participants. The fix defines a canonical, sorted transcript over state plus tagged cap groups. Treat lengths, empty groups, and type tags as transcript data, not parser metadata.

## Regression

Permute groups or change a family/type/state word while preserving caps and assert a different memory challenge seed.

```sh
git diff 6be5025cc072e7ae503726a77d4cc0be1fd59577 386ab2621f484cd8d923acbbf3e00467c8bd46ae -- circuit_defs/trace_and_split/src/lib.rs full_statement_verifier/src/unrolled_proof_statement.rs
```
