# Zero-width base cap changed the GPU transcript

## Classification

- Producer-parity history: confirmed optional/empty-message transcript bug
- Component: GKR base commitments and WHIR proof parsing for standalone inits/teardowns
- Security character: confirmed honest-proof rejection/completeness failure
  confined to a reachable width-zero layout
- Fixed by: [`6bd4fdf`](https://github.com/matter-labs/zksync-airbender/commit/6bd4fdf42071903e8f3033b472ee20aee7bab180)
- Vulnerable revision: `eac16fe5cf56dfdda86d44beccf2597a97b70cd6`

## Protocol context

The standalone inits-and-teardowns circuit is a special cache-layout circuit whose witness base layer has width zero and whose setup layer is absent. The CPU protocol treats a width-zero oracle as no transcript message: its dummy tree has an empty cap and no queries.

Optional protocol objects require a canonical convention. “No oracle,” “an empty cap,” and “a fixed-size cap filled by a degenerate tree” are different byte streams even if all three represent zero columns to local code.

## Intended transcript relation

For each base oracle independently:

```text
if declared column width > 0:
    serialize cap
    absorb cap
    later parse/verify queries
else:
    serialize no cap digests
    perform no cap absorption
    parse/verify no queries
```

CPU prover, GPU prover, Rust verifier, recursive verifier, and generated/L1 consumers must use the same width predicate and empty representation.

## Failure

The GPU path had two width-zero-only defects:

1. Initial transcript construction gated the setup cap but absorbed memory and witness caps unconditionally. It therefore absorbed a dummy witness cap that the CPU/verifier omitted.
2. WHIR proof parsing emitted a degenerate 16-digest cap for the zero-column witness oracle, while the CPU dummy tree represented that cap as empty. Query parsing was already correctly gated.

The forward output claims remained equal because this circuit drew no challenge between the initial commit phase and the post-forward evaluation point. From that point onward, however, the seed, backward sumcheck, and WHIR proof diverged.

## Failure flow

1. Select the standalone inits/teardowns layout with `witness_layout.total_width == 0`.
2. GPU absorbs/serializes a dummy witness cap.
3. CPU/canonical verifier performs no event for that oracle.
4. Both compute the same seed-independent forward values, hiding the defect.
5. The next evaluation-point squeeze differs and every later algebraic message follows a different challenge path.

This historical case is an honest-proof completeness/parity failure, not evidence that the canonical verifier accepted an unbound nonempty oracle. It is nevertheless security-sensitive protocol engineering because a verifier port with a different empty convention can fork the accepted proof language.

## Impact and fix

Only the zero-width path produced different proof bytes and challenges, which let normal multi-column tests pass. The fix gates memory/witness cap absorption on their declared layout widths and emits an empty cap when `num_columns == 0`, matching the existing query gate and CPU behavior.

Optional messages must be specified as an explicit transcript grammar. Do not infer their presence from whether an implementation happened to allocate a placeholder object.

## Regression

- Run byte-exact CPU/GPU proof and transcript parity at widths 0, 1, and a normal multi-column width.
- Assert zero width produces zero cap digests, zero absorption events, and zero queries.
- Compare seeds immediately after every base-oracle slot, including omitted slots.
- Test all combinations of setup, memory, and witness presence rather than only the currently reachable one.
- Reject a proof that supplies a nonempty cap for a declared zero-width oracle.

## Reproduction evidence

The same-revision flattener and generated verifier both gate cap parsing on
`num_columns > 0`; the standalone inits/teardowns witness layout has zero
columns. The fix commit records byte-exact CPU/GPU proof-parity failure before
the fix and passing parity afterward:

```sh
git diff eac16fe5cf56dfdda86d44beccf2597a97b70cd6 6bd4fdf42071903e8f3033b472ee20aee7bab180 -- gpu/circuit_prover/src/prover/proof/orchestration/stage1_forward.rs gpu/circuit_prover/src/prover/proof_layout/accessors.rs
git show eac16fe5cf56dfdda86d44beccf2597a97b70cd6:verifier_common/src/gkr/flatten.rs
git show eac16fe5cf56dfdda86d44beccf2597a97b70cd6:verifier_generator/src/gkr/mod.rs
```
