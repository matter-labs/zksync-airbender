# UNIFIED: Unified execution layout

> Places active machine cycles into instances of one unified execution circuit.
> Logical cycle semantics are owned by [common execution](common.md); ISA-family
> equations and delegated fulfillment traces are outside this module.

`*` marks a provisional relation whose accepted proof-structure binding remains
open.

## Guarantee

All active CPU cycles use the same unified circuit shape. On each active row, decoder
data selects exactly one admitted ISA family inside that circuit. The proof supplies
the profile-selected number of fixed-capacity chunks and pads only the unused suffix
of the final chunk.

The semantic choice of ISA family is the same unique authenticated choice as in the
shared execution relation. Only its physical realization differs from the unrolled
layout.

## Symbols and inputs

- **IN-UNIFIED-001 — Family inventory.** `P` is the selected unified proof profile,
  and `F(P)` is the set of ISA families admitted inside its unified circuit
- **IN-UNIFIED-002* — Proof structure.** `Q = (Q_0, ..., Q_q-1)` is the sequence of
  `q` supplied unified chunks
- **IN-UNIFIED-003 — Chunk capacity.** `K_P` and its chunk-count rule are selected by
  the execution profile
- `execute_j,k ∈ {0, 1}` — activation flag of row `k` in chunk `j`
- `sel_j,k,f ∈ {0, 1}` — row selector for `f ∈ F(P)`
- `cycles = Σ_j Σ_k execute_j,k` — number of active rows

The bridge and unified-recursion profiles currently select `K_P = 2²³`. The
experimental L1 profile selects one chunk with `K_P = 2²²`.

## Assumptions

- **ASM-UNIFIED-001 — Shared cycle relation.** Every active row satisfies
  `REL-EXEC-001..007`.
- **ASM-UNIFIED-002 — Unified decoder.** An active row's authenticated decoder data
  binds the in-circuit family selector.
- **ASM-UNIFIED-003* — Verifier structure binding.** The verifier accepts exactly the
  unified chunks declared for this proof instance and includes all of them in the
  shared argument closure.

## Canonical relation tree

> Interpret this tree under `ASM-UNIFIED-001..003`. Relations on the same branch are
> conjoined.

- **Unified proof structure — [`REL-UNIFIED-002`] Chunk count**
  - **Bridge or unified-recursion profile**
    `q = ⌈cycles / K_P⌉`
  - **Experimental L1 profile**
    `q = 1 ∧ cycles ≤ K_P`
- **Supplied unified chunk — [`REL-UNIFIED-003`] Final-chunk padding**
  Every supplied chunk has exactly `K_P` rows. For profiles using the ceiling
  chunk-count rule, every row of every non-final chunk is active and the final chunk
  consists of an active prefix followed by an inactive suffix. The experimental L1
  profile applies the same rule to its single chunk
  - **Active row — [`REL-UNIFIED-001`] In-circuit family selection**
    ```text
    Σ_(f ∈ F(P)) sel_j,k,f = 1
    sel_j,k,f = 1 ⇒ the authenticated decoder data selects f
    ```

    The selected family relation governs the row's cycle transition
  - **Inactive row.** Every family selector is `0` and the row satisfies
    `REL-EXEC-004`
- **All supplied unified chunks — [`OUT-UNIFIED-001`]* Unified row collection**
  The accepted chunks supply the physical rows consumed by `EXEC`, and every supplied
  active row participates in the shared state and argument closure

## Open boundary

- **GAP-UNIFIED-001 — Accepted unified chunk structure.** Specify where `q` and the
  selected unified profile are encoded, how the verifier binds them to the accepted
  chunks, and which argument establishes that their active rows are the complete
  logical execution.

## Metadata

- spec revision: TBD
- implementation: `matter-labs/zksync-airbender@87b9d98ce+dirty`
- profile: bridge-unified-reduced, recursion-unified-reduced, and l1-proth120

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-UNIFIED-001` | normative | — | — | prose | [unified ISA profile](../isa/unified/profile.md); [proof profiles](../profiles/INDEX.md) | — |
| `IN-UNIFIED-002` | provisional | — | `GAP-UNIFIED-001` | prose | current execution design | — |
| `IN-UNIFIED-003` | normative | — | selected execution profile | prose | [hierarchy](../HIERARCHY.md); [proof profiles](../profiles/INDEX.md) | — |
| `ASM-UNIFIED-001` | normative | all supplied rows | `REL-EXEC-001..007` | prose | [common execution](common.md) | — |
| `ASM-UNIFIED-002` | normative | active unified row | `REL-EXEC-001`, `REL-EXEC-003`, `REL-EXEC-005` | prose | [common execution](common.md); current unified ISA organization | — |
| `ASM-UNIFIED-003` | provisional | all supplied chunks | `GAP-UNIFIED-001` | prose | proof-format binding not yet reconciled | — |
| `REL-UNIFIED-001` | normative | every supplied row | `ASM-UNIFIED-001..002`; `IN-UNIFIED-001` | prose | [hierarchy](../HIERARCHY.md); current unified execution design | — |
| `REL-UNIFIED-002` | normative | selected unified profile | `IN-UNIFIED-002..003` | prose | [hierarchy](../HIERARCHY.md); [proof profiles](../profiles/INDEX.md) | — |
| `REL-UNIFIED-003` | normative | each supplied chunk | `REL-EXEC-004`; `REL-UNIFIED-002` | prose | `decision:execution-structure-2026-09-04`; [hierarchy](../HIERARCHY.md) | — |
| `OUT-UNIFIED-001` | provisional | all supplied chunks | `ASM-UNIFIED-003`; `REL-UNIFIED-001..003`; `GAP-UNIFIED-001` | prose | derived from the unified layout relations above | — |
| `GAP-UNIFIED-001` | open | — | affects `IN-UNIFIED-002`, `ASM-UNIFIED-003`, and `OUT-UNIFIED-001`; owner: human | — | exact proof-structure and completeness binding not yet reconciled | — |
