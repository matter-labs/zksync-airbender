# UNROLLED: Unrolled execution layout

> Places active machine cycles into family-specific circuit chunks. Logical cycle
> semantics are owned by [common execution](common.md); ISA-family equations and
> delegated fulfillment traces are outside this module.

`*` marks a provisional relation whose accepted proof-structure binding remains
open.

## Guarantee

The selected ISA profile fixes the admitted unrolled circuit families. A chunk's
circuit identity fixes its family; each active row authenticates an instruction of
that family. For each family, the proof supplies the profile-selected number of
fixed-capacity chunks and pads only the unused suffix of the final chunk.

Family chunks need not establish logical adjacency by their physical row order. The
shared execution and global state arguments establish the logical cycle chain across
families and chunks.

## Symbols and inputs

- **IN-UNROLLED-001 — Family inventory.** `P` is the selected unrolled proof profile,
  and `F(P)` is the set of unrolled circuit families admitted by its ISA profile
- **IN-UNROLLED-002* — Proof structure.**
  `Q_f = (Q_f,0, ..., Q_f,q_f-1)` is the sequence of `q_f` chunks supplied for
  family `f`
- **IN-UNROLLED-003 — Chunk capacity.** `K_f` is the profile-selected row capacity
  of one execution chunk for family `f ∈ F(P)`
- `execute_f,j,k ∈ {0, 1}` — activation flag of row `k` in chunk `j` for family `f`
- `calls_f = Σ_j Σ_k execute_f,j,k` — number of active rows supplied for family `f`

The base and unrolled-recursion profiles currently select `K_f = 2²⁴` for CPU
instruction-family chunks. Delegated fulfillment circuits own their separate
capacities in their ISA modules.

## Assumptions

- **ASM-UNROLLED-001 — Shared cycle relation.** The supplied rows are governed by
  `REL-EXEC-001..006`; every active row satisfies its active-cycle clauses.
- **ASM-UNROLLED-002 — Family decoder.** An active row in a family-`f` circuit can
  authenticate only decoder data selecting `f`.
- **ASM-UNROLLED-003* — Verifier structure binding.** The verifier accepts exactly
  the family chunk collections declared for this proof instance and includes all of
  them in the shared argument closure.

## Canonical relation tree

> Interpret this tree under `ASM-UNROLLED-001..003`. Relations on the same branch are
> conjoined.

- **Supplied chunk family — [`REQ-UNROLLED-001`] Admitted family**
  Every supplied execution chunk has exactly one family label `f`
  - **`f ∉ F(P)`.** Violates `REQ-UNROLLED-001`
  - **`f ∈ F(P)`**
    - **[`REL-UNROLLED-002`] Family chunk count**
      `q_f = ⌈calls_f / K_f⌉`

      If `calls_f = 0`, then `q_f = 0`
    - **[`REL-UNROLLED-003`] Final-chunk padding**
      Every supplied chunk has exactly `K_f` rows. Every row of every non-final chunk
      is active. The final chunk consists of an active prefix followed by an inactive
      suffix
      - **Active row — [`REL-UNROLLED-001`] Family-specific execution**
        The authenticated decoder data selects family `f`, and the row applies that
        family's admitted ISA relation

        The circuit identity realizes the family selection. There is no additional
        in-row choice among different circuit families
      - **Inactive row.** Satisfies `REL-EXEC-004`
- **All supplied family chunks — [`OUT-UNROLLED-001`]* Unrolled row collection**
  The accepted chunks supply the physical rows consumed by `EXEC`, and every supplied
  active row participates in the shared state and argument closure

## Open boundary

- **GAP-UNROLLED-001 — Accepted family chunk structure.** Specify where `q_f` and the
  supplied family inventory are encoded, how the verifier binds them to the accepted
  chunks, and which argument establishes that the union of their active rows is the
  complete logical execution. Do not assume an explicit cycle-to-chunk permutation if
  the PC-state and other global arguments establish this implicitly.

## Metadata

- spec revision: TBD
- implementation: `matter-labs/zksync-airbender@303ea6fa+dirty`
- profile: base-unrolled-full-unsigned and recursion-unrolled-reduced

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-UNROLLED-001` | normative | — | — | prose | [unrolled ISA profile](../isa/unrolled/profile.md); [proof profiles](../profiles/INDEX.md) | — |
| `IN-UNROLLED-002` | provisional | — | `GAP-UNROLLED-001` | prose | current execution design | — |
| `IN-UNROLLED-003` | normative | — | selected execution profile | prose | [hierarchy](../HIERARCHY.md); [proof profiles](../profiles/INDEX.md) | — |
| `ASM-UNROLLED-001` | normative | all supplied rows | `REL-EXEC-001..006` | prose | [common execution](common.md) | — |
| `ASM-UNROLLED-002` | normative | active family row | `REL-EXEC-001..002`, `REL-EXEC-004` | prose | [common execution](common.md); current unrolled ISA organization | — |
| `ASM-UNROLLED-003` | provisional | all supplied chunks | `GAP-UNROLLED-001` | prose | proof-format binding not yet reconciled | — |
| `REL-UNROLLED-001` | normative | active family row | `ASM-UNROLLED-001..002`; `IN-UNROLLED-001` | prose | `decision:execution-structure-2026-09-04`; [hierarchy](../HIERARCHY.md) | — |
| `REL-UNROLLED-002` | normative | each admitted family | `IN-UNROLLED-002..003` | prose | [hierarchy](../HIERARCHY.md) | — |
| `REL-UNROLLED-003` | normative | each supplied chunk | `REL-EXEC-004`; `REL-UNROLLED-002` | prose | `decision:execution-structure-2026-09-04`; [hierarchy](../HIERARCHY.md) | — |
| `REQ-UNROLLED-001` | normative | each supplied chunk | `IN-UNROLLED-001..002` | prose | selected unrolled profile | — |
| `OUT-UNROLLED-001` | provisional | all supplied chunks | `ASM-UNROLLED-003`; `REL-UNROLLED-001..003`; `REQ-UNROLLED-001`; `GAP-UNROLLED-001` | prose | derived from the unrolled layout relations above | — |
| `GAP-UNROLLED-001` | open | — | affects `IN-UNROLLED-002`, `ASM-UNROLLED-003`, and `OUT-UNROLLED-001`; owner: human | — | exact proof-structure and completeness binding not yet reconciled | — |
