# Machine-state permutation challenges were not continuous across circuit proofs

## Classification

- Confirmed historical inter-circuit soundness bug
- Components: unified and unrolled full-statement verifiers
- Bug class: missing cross-proof equality checks after refactoring
- Fixed by: [`4844b40`](https://github.com/matter-labs/zksync-airbender/commit/4844b40a57e8b04189cf8587170469b9b7d61274), PR [#258](https://github.com/matter-labs/zksync-airbender/pull/258)
- Vulnerable revision for reproduction: `73f46c2bc86cdcefb878d6675abfcfc0eaf04607`

## Intended relation

All chunks and circuit families contributing to one full machine statement must use the same transcript-derived random challenges for each shared permutation argument. In particular, machine-state `(pc,timestamp)` contributions can be multiplied across proofs only when their linearization challenges and additive term are identical. Memory and delegation challenges have analogous continuity obligations where used.

## Vulnerable relation

After a verifier refactor, the unified path compared memory and delegation challenges between adjacent chunks but omitted `machine_state_permutation_challenges`. The unrolled path compared some challenges only within repeated instances of one family and then used whichever scratch output remained as the reference across families. Comments incorrectly assumed the called verifier functions preserved this external continuity.

## Security impact

Grand-product accumulators from independently valid circuit proofs could be combined even though they encoded machine states under different randomizers. Their product no longer represented one global permutation argument, so local proofs did not establish a single continuous execution across chunks and circuit families.

## Fix

The unified verifier now compares machine-state challenges between chunks. The unrolled verifier records an explicit reference proof output, compares every applicable circuit family and initialization/delegation proof against it, and compares that reference with challenges derived from the full transcript. It also requires a nonempty initialized execution before those comparisons.

## Audit lesson

List inter-circuit obligations separately from local constraints and follow them through refactors. For every accumulator, record its tuple encoding, challenge source, and equality checks across chunks, families, initialization/teardown proofs, and delegation proofs.

## Regression test

- Build a verifier-level test harness with two valid circuit proofs and assert rejection whenever one shared challenge field differs.
- Cover repeated unified chunks, transitions between different unrolled families, and initialization/teardown proofs.
- Assert that the final transcript-derived challenge is compared with the same explicit reference used for all accumulated contributions.

## Reproduction evidence

```sh
git diff 73f46c2bc86cdcefb878d6675abfcfc0eaf04607 4844b40a57e8b04189cf8587170469b9b7d61274 -- \
  full_statement_verifier/src/unified_circuit_statement.rs \
  full_statement_verifier/src/unrolled_proof_statement.rs
```
