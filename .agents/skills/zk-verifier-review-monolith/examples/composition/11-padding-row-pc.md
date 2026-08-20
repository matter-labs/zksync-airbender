# Padding rows used PC zero instead of PC_STEP

## Classification

- Confirmed historical padding-state bug
- Invariant: inactive rows use the circuit's canonical neutral global-state encoding
- Component: GPU `jump_branch_slt` witness padding
- Security character: CPU/GPU proof parity and global-state commitment failure
- Fixed by: [`e5815c5`](https://github.com/matter-labs/zksync-airbender/commit/e5815c54f8a185592fb4a190cd7b7f6a3927d782)
- Vulnerable revision: `dad06de77cfa01d2734a7b39c9113de480a3bc17`

## Composition context

Fixed-size traces pad unused rows to a power-of-two length. Padding is not “don't care” data: every committed column receives concrete values, and constraints/global arguments define a precise neutral row that must not introduce RAM, PC, timestamp, or delegation state.

For the jump/branch/SLT family, CPU setup used the shared `PC_STEP = 4` convention for a padding PC-related field. The GPU witness generator had a stale literal zero.

## Intended invariant

For every inactive row of a circuit family:

```text
active/padding selector has canonical inactive value
all local constraints are satisfied
RAM/delegation contributions are neutral
PC/timestamp/state fields equal the setup-defined padding constants
CPU and GPU produce identical committed rows
```

Neutrality must be checked in the global argument representation, not inferred from a disabled local gate.

## Failure

GPU `jump_branch_slt` padding rows wrote PC zero while CPU setup and canonical witness logic used `PC_STEP`. The resulting row could satisfy enough local padding behavior to escape an immediate assertion, yet it changed a committed state column and therefore the memory cap and all transcript-derived challenges.

The existing parity fixture initially failed to expose the bug because it supplied the same GPU-side constant to its CPU oracle. The end-to-end program prover, which reconstructed the independent canonical setup, revealed the mismatch.

## Failure flow

1. Produce a chunk with at least one padding row in the affected family.
2. GPU writes zero into the padding PC field.
3. CPU/canonical setup expects four.
4. The committed base layer and Merkle cap differ.
5. Every challenge after cap absorption and the resulting proof diverge; global PC/state semantics may also include a noncanonical padding contribution depending on selectors.

The historical evidence is an honest proof/parity failure. A separate soundness analysis must verify that all padding selectors algebraically neutralize global contributions so an attacker cannot choose arbitrary committed padding state.

## Impact and fix

Affected padded GPU traces did not match canonical setup and could not produce verifier-compatible proofs. The fix references the shared `PC_STEP` constant rather than duplicating a literal.

Padding audits should enumerate every committed field and every global-argument contribution. Cross-implementation tests must derive expected constants from the specification or independent CPU path, not feed the device value back as the oracle.

## Regression

- For every circuit family, compare full CPU/GPU padding rows and committed caps.
- Force zero, one, and many padding rows around the exact-capacity boundary.
- Mutate each padding state field independently and require either constraint failure or unchanged proven global contribution only when neutrality is explicitly established.
- Source canonical constants from shared setup/spec code in production while keeping an independent literal/spec oracle in tests.
- Include end-to-end verifier parity, not only witness-structure equality.

## Reproduction evidence

```sh
git diff dad06de77cfa01d2734a7b39c9113de480a3bc17 e5815c54f8a185592fb4a190cd7b7f6a3927d782 -- gpu/circuit_prover/src/witness/circuit_type.rs
```
