# Recursive proof output was not bound to the supplied program

## Classification

- Confirmed historical recursion-anchoring soundness bug
- Boundary: cryptographically authenticated recursive output → `cli verify` claim that the proof belongs to the supplied `--bin`/`--text`
- Component: `verify_artifact` across base, unrolled, and unified recursion targets
- Security character: valid-proof replay/substitution across programs sharing a program-independent recursion verifier
- Fixed by: [`a2d7ad1`](https://github.com/matter-labs/zksync-airbender/commit/a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0), PR [#321](https://github.com/matter-labs/zksync-airbender/pull/321)
- Vulnerable revision: `180c1c336e4c939e57a54559e0d507e8ef359745`

## Boundary context

The recursive verifier setup is intentionally reusable and therefore does not identify one application program by itself. Program identity is carried through a recursion-chain hash in authenticated verifier output—historically `output[8..16]`. Separately, the serialized artifact contains editable metadata such as program binary/text hashes and a copy of recursion-chain-related data.

Only values returned by successful proof verification are authenticated. Recomputing the expected chain from the supplied program is useful only if the verifier compares it with the authenticated output, not with another field read from the artifact.

## Intended anchoring contract

For every accepted target shape:

```text
verified_output = verify_recursive_proof(proof, trusted_setup_for_stage)
authenticated_chain = verified_output[8..16]
expected_chain = derive_chain(supplied_program, exact_recursion_stage)
require authenticated_chain == expected_chain
```

The comparison must cover direct base proofs, unrolled-over-base, unrolled-over-prior-unrolled, and unified branches. A branch-specific omission is a replay surface.

## Failure

CLI verification checked editable artifact metadata and successfully ran a program-independent recursion verifier, but discarded the authenticated recursion chain returned in `output[8..16]`. Program-derived level hashes were computed during setup/model construction yet never compared with that output.

The artifact's own `recursion_chain_hash` could not substitute for this check: it was serialized prover input describing the chain fed into recursion, not the verifier's authenticated result.

## Adversarial flow

1. Produce a valid recursive proof for program Q.
2. Copy it into an artifact presented as program P.
3. Rewrite editable program hash/metadata fields so superficial metadata checks describe P.
4. CLI verifies the recursion proof using the reusable verifier setup.
5. The authenticated output still names Q, but the CLI discards that slice.
6. Verification reports success for P.

No cryptographic primitive is broken; the verifier proves one statement and the wrapper labels it as another.

## Impact and fix

A valid recursive proof for program Q could be relabeled and accepted for program P. The fix introduces a shared comparison of the verifier-derived output chain with the expected program-derived chain and invokes it in every base, unrolled, and unified target branch.

This finding is established at the CLI verification boundary. The historical
change does not by itself establish that an L1 settlement contract used the CLI
or shared the same omission.

The general review rule is to label every value by provenance: trusted caller input, prover-controlled artifact metadata, or authenticated verifier output. Equality between two prover-controlled copies does not anchor a recursive statement.

## Regression

- Verify one proof against its actual program, then relabel metadata and attempt verification against a distinct program using the same recursion verifier.
- Mutate the artifact's copied chain while preserving the proof and ensure it never substitutes for authenticated output.
- Cover every source/target recursion branch, including direct base and both unrolled input shapes.
- Check all eight output limbs and their canonical encoding/order.
- Add a program whose metadata hashes are distinct but whose recursion verifier setup is intentionally identical.

## Reproduction evidence

```sh
git diff 180c1c336e4c939e57a54559e0d507e8ef359745 a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0 -- tools/cli/src/prover_utils.rs
```
