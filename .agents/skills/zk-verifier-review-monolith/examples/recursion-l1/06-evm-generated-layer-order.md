# Generated EVM verifier skipped layer 4 and used a stale output permutation

## Classification

- Confirmed soundness bug in the runnable `av_large_field` generated/test contract
- Boundary: `GKRCircuitArtifact` semantics → assembled Solidity/Yul verifier
- Component: circuit layer call graph and dimension-reduction boundary permutation
- Verifier anchor: assembled Solidity/Yul verifier driver emitted by `verifier_evm/src/generator/assemble.rs`
- Security character: the emitted artifact had five layers, but the driver called only layers 3 through 0; global-output offsets were also stale
- Fixed by: [`5459c07`](https://github.com/matter-labs/zksync-airbender/commit/5459c07f94f5b6c843c0cb405ee797a4b2e93e7f)
- Vulnerable revision: `1500f8ba394ecc320955493ac12d4030ffd20271`

The vulnerable revision committed generated contracts, real calldata fixtures,
and the Foundry two-transaction harness. No production deployment is established.

## Boundary context

The artifact defines the number of GKR layers and maps logical output types to concrete `GKRAddress::InnerLayer` offsets. Verification runs layers backward—from highest/output layer to layer zero—and then reorders the boundary LSB values into logical output order for memory, lookup, and inits/teardowns accumulators.

The old EVM driver encoded both structures as template literals independent of the artifact used to emit per-layer functions.

## Intended artifact contract

```text
for i in (0 .. artifact.layers.len()).reverse():
    call sumcheck_circuit_layer_i exactly once

SI[logical_output_position] = artifact.global_output_map[OutputType][position].offset
```

Generation must fail if output addresses are not the expected layer kind/count or if template markers are absent.

## Failure

The vulnerable generated contract contained
`sumcheck_circuit_layer4`, but its driver called only layers `3, 2, 1, 0`.
It therefore omitted a concrete emitted proof layer rather than merely risking
future drift. Its boundary permutation was the stale
`[6,7,0,1,2,3,4,5,8,9]`; regeneration from the artifact produced
`[2,3,0,1,4,5,6,7,8,9]`.

## Adversarial or failure flow

1. Use the committed five-layer artifact and generated contract.
2. Enter the hardcoded driver after the dimension-reduction claim.
3. Skip layer 4 entirely and begin verification at layer 3.
4. Route boundary values with the stale logical-output permutation.
5. Reach the remaining GKR/WHIR and terminal checks for a reduction chain that is
   not the five-layer artifact's claim chain.

This is a generated-verifier soundness failure at the branch's contract/test
boundary. Source generator fixes do not repair any already compiled runtime.

## Impact and fix

The accepted on-chain proof language could drift from the selected circuit artifact. The fix adds generator markers, emits reverse layer calls from `circuit.layers.len()`, derives the ten-entry boundary permutation from `global_output_map`, validates address types/count, and fails if markers remain.

Generated verifier audits need reproducible provenance from artifact through template substitution to compiled runtime hash. Do not treat templates as authoritative when assembly injects semantic control flow.

## Regression

- Regenerate after adding/removing a layer and compare the exact call graph.
- Permute output addresses and verify logical memory/lookup/I/T slots follow the artifact.
- Assert every emitted layer function is called exactly once in reverse order.
- Fail generation on missing markers, wrong output count, or unexpected address variants.
- Compare generated source and deployed runtime fingerprint for the audited artifact.

## Reproduction evidence

```sh
git diff 1500f8ba394ecc320955493ac12d4030ffd20271 5459c07f94f5b6c843c0cb405ee797a4b2e93e7f -- verifier_evm/src/generator/assemble.rs verifier_evm/src/generator/circuit_yul.rs
```
