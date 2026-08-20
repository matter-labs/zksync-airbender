# Generated EVM verifier hardcoded layer count and output order

## Classification

- Confirmed historical generated-artifact drift bug
- Boundary: `GKRCircuitArtifact` semantics → assembled Solidity/Yul verifier
- Component: circuit layer call graph and dimension-reduction boundary permutation
- Security character: omitted/stale layer or misowned global outputs; exact result ranges from honest rejection to wrong accepted circuit
- Fixed by: [`5459c07`](https://github.com/matter-labs/zksync-airbender/commit/5459c07f94f5b6c843c0cb405ee797a4b2e93e7f)
- Vulnerable revision: `1500f8ba394ecc320955493ac12d4030ffd20271`

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

The assembled contract hardcoded which `sumcheck_circuit_layer{i}` functions were called and hardcoded the boundary LSB reorder. Circuit depth and `global_output_map` ordering had changed independently.

This could leave an emitted layer function uncalled, call a stale/nonexistent layer sequence, or route correct output values into the wrong global accumulator slots. A separate minor issue in the same update explicitly initialized the generated Horner accumulator to zero.

## Adversarial or failure flow

1. Modify/recompile the circuit artifact by adding/removing a layer or reassigning output offsets.
2. Emit new per-layer Yul functions from that artifact.
3. Assemble them with a driver retaining old hardcoded calls/permutation.
4. Skip a layer's proof or interpret a lookup/memory output as another type.
5. Reach global terminal checks for a circuit different from the artifact the deployment intends—or reject all honest proofs if inconsistency is detected later.

Reachability depends on the exact generated contract deployed. Source generator fixes do not repair already compiled runtime bytecode.

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
