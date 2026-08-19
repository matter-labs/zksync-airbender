# Batching challenge lived inside an optional cache branch

## Classification

- Confirmed historical optional-path challenge bug
- Component: GKR sumcheck layer transition
- Fixed by: [`2df0dea`](https://github.com/matter-labs/zksync-airbender/commit/2df0dea2b68bd6ab6070484277feb9d16435c934)
- Vulnerable revision: `9050461d9830eb83405b683ae526e635bc91d3a5`

## Failure

After the extra-evaluation ordering repair, the absorb-and-draw sequence remained inside the `cache_relations` branch. Layers without caches did not execute the canonical transition at the same scope.

## Impact and fix

Transcript evolution depended on an implementation branch rather than the protocol round, risking missing or uninitialized next-layer randomness. The fix moves the single absorb-and-draw after the branch so every layer follows it exactly once.

## Regression

Compare transcript event traces for structurally identical layers with zero and one cache relation; only the absorbed extra payload may differ.

```sh
git diff 9050461d9830eb83405b683ae526e635bc91d3a5 2df0dea2b68bd6ab6070484277feb9d16435c934 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
