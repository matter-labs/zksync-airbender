# Verification policy came from prover-controlled metadata

## Classification

- Confirmed historical CLI acceptance-policy bug
- Boundary: untrusted proof artifact → `cli verify`/`continue-proof` selection of security level, recursion target, and binary/model
- Component: CLI `verify` and `continue-proof` policy plumbing
- Security character: policy downgrade and stage confusion before cryptographic verification
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Boundary context

A proof artifact may truthfully describe how it was produced, but those fields are still attacker-controlled input at verification time. The relying party's required security level and acceptable terminal target are authorization policy. They must arrive through a trusted channel and choose the verification model, recursion binaries, expected chain, and convergence rules.

The safe direction is:

```text
trusted policy -> select verifier/configuration
artifact metadata -> parse and require equality with trusted policy
proof -> verify under selected configuration
```

Letting metadata select the verifier reverses the trust boundary even if the proof is valid under the selected weaker configuration.

## Failure

`verify` and parts of `continue-proof` selected `security_level`, target, recursion binaries, and verification flow from fields inside the proof artifact. A caller asking “is this an acceptable final proof?” did not independently provide the expected values.

## Adversarial flow

1. Produce a valid proof under a supported but weaker security schedule or at a different accepted recursion stage.
2. Serialize matching weak `security_level`/`target` metadata in the artifact.
3. Submit the artifact to a consumer that intended the stronger/final policy.
4. The CLI reads attacker metadata and chooses the weaker model/binary/verification branch.
5. Cryptographic verification succeeds for the weaker statement.
6. The wrapper reports success without ever comparing against the relying party's intended policy.

The proof need not be malformed. The bug is that “valid under some supported policy” was treated as “valid under the policy required here.”

## Impact and fix

An artifact could steer the generic CLI success result into a weaker security
schedule or a different stage than the relying caller intended. The fix requires
explicit trusted `--security-level` and `--target` inputs (and trusted security
policy for proof continuation), chooses the configuration from those values, and
rejects artifacts whose descriptive metadata disagrees.

The proof remains valid under the weaker policy it names; the unauthorized
transition is the wrapper reporting success against an unstated stronger/final
policy. This is a CLI/relying-party boundary finding, not evidence of a deployed
L1 contract downgrade.

The same rule applies to L1 deployments: contract address, verifier key, circuit/version identifier, recursion depth, and expected public-input schema are policy, not calldata-selected conveniences.

## Regression

- Present artifacts whose target and security level independently disagree with trusted caller inputs; require rejection.
- Cross the matrix of every supported security level and recursion target, including valid proofs for the wrong cell.
- Assert trusted policy selects binaries/models before artifact metadata is consumed as anything but a consistency check.
- Apply the same tests to `verify`, `continue-proof`, APIs, and settlement wrappers.
- Add a new supported policy only together with an explicit caller-facing selection and mismatch test.

## Reproduction evidence

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- tools/cli/src/main.rs tools/cli/src/prover_utils.rs
```
