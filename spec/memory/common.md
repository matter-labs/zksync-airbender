# MEM: Common memory relation

> Partial integration of shared ROM/RAM semantics and the global state-permutation
> argument.

`*` marks a provisional relation whose complete integration with ROM/RAM and the
profile-specific initialization/teardown modules remains open.

## PC-state permutation

- `cycles`, `PCState`, and each `cycle.text` and `cycle.timestamp` come from the
  [common execution relation](../execution/common.md)
- `PCReads` and `PCWrites` are multisets; their comprehensions retain multiplicity
- `⊎` denotes multiset union
- `PCRead(cycle) = (PC, PCState[cycle.timestamp], cycle.timestamp)`
- `PCWrite(cycle) = (PC, PCState[cycle.timestamp + 4], cycle.timestamp + 4)`
- `PCInitial = (PC, 0, 4)`
- `PCFinal = (PC, exit_pc, 4 + 4 · |cycles|)`

### REL-MEM-001* — PC-state closure

```text
PCReads  = {PCRead(cycle) | cycle ∈ cycles} ⊎ {PCFinal}
PCWrites = {PCInitial} ⊎ {PCWrite(cycle) | cycle ∈ cycles}

PCReads = PCWrites
```

Together with each cycle ending at `cycle.timestamp + 4`, bounded non-wrapping
timestamps make these records one chain from `PCInitial` to `PCFinal`. In particular:

`{q ∈ u32 | (PC, q, 0) ∈ PCReads ⊎ PCWrites} = ∅`

## Intended contents

- address and value domains
- ROM reads and RAM reads/writes
- ordering and timestamp rules
- global permutation or grand-product closure
- initial and final architectural memory state

Current material remains in [machine-old/memory.md](../machine-old/memory.md).

## Open boundary

- **GAP-MEM-001 — Complete state-permutation integration.** Integrate register and
  RAM records, profile-specific initialization/teardown, challenge derivation, and
  aggregate product equality with `REL-MEM-001`.

## Metadata

- spec revision: draft
- implementation: `zksync-airbender@303ea6fa+dirty`
- profile: unrolled and unified execution

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REL-MEM-001` | provisional | proof acceptance | `external:EXEC`; `GAP-MEM-001` | located | current PC-state grand-product construction and verifier boundary injection | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `GAP-MEM-001` | open | — | affects `REL-MEM-001` and remaining common-memory scope; owner: human | — | common memory module remains partially integrated | — |
