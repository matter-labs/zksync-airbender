# GP-VER: Global-product verifier obligations

> Accepts one declared collection of partition-product pairs. The caller owns the
> partition inventory and any boundary tuples included in it.

## Imports

- `arguments/global-products/relation.md`

## Assumptions

- **ASM-GP-VER-001 — Partition-product correctness.** The consuming proof protocol
  establishes each supplied pair as the products of its declared tuple partitions
  under the common `χ`.
- **ASM-GP-VER-002 — Complete inventory.** The caller fixes the complete ordered list
  of partition-product pairs before verification.

## Requirements

### REQ-GP-VER-001 — Accumulate every partition

Initialize `(P_R, P_W) = (1, 1)`. For every pair `(P_R[i], P_W[i])` in the inventory,
update

`P_R ← P_R · P_R[i]`

`P_W ← P_W · P_W[i]`.

Consume every declared pair exactly once and reject missing or trailing pairs.

### REQ-GP-VER-003 — Bound challenge vector

Derive `χ` only after every value on which the tuples depend is bound. Require every
partition-product proof to use that same `χ`.

### REQ-GP-VER-005 — Terminal equality

After `REQ-GP-VER-001`, reject unless

`P_R = P_W`.

No nonzero-product check is required; zero factors are covered by
`REQ-GP-SND-002`.

## Rejections

- **REJ-GP-VER-004 — Inventory mismatch.** Reject if the supplied partition-product
  list differs from the inventory fixed by `ASM-GP-VER-002`.
- **REJ-GP-VER-002 — Challenge mismatch.** Reject if a partition product uses a
  challenge vector other than the one fixed by `REQ-GP-VER-003`.
- **REJ-GP-VER-003 — Product mismatch.** Reject if the terminal products differ.

## Output

- **OUT-GP-VER-001 — Accepted product identity.** Acceptance establishes
  `REQ-GP-REL-004..005` for the caller's declared partitions.

## Metadata

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-GP-VER-001` | normative | every partition-product pair | discharged per proof by `OUT-GKR-VER-002` | partition-product correctness |
| `ASM-GP-VER-002` | normative | one product instance | external boundary: calling relation | complete partition inventory |
| `REQ-GP-VER-001` | normative | every partition-product pair | `ASM-GP-VER-001..002`, `REQ-GP-REL-002` | product aggregation |
| `REQ-GP-VER-003` | normative | one product instance | `REQ-GP-REL-001` | challenge binding |
| `REQ-GP-VER-005` | normative | proof acceptance | `REQ-GP-VER-001`, `REQ-GP-VER-003`, `REQ-GP-REL-004` | terminal product comparison |
| `REJ-GP-VER-004` | normative | partition parsing | derived from `ASM-GP-VER-002`, `REQ-GP-VER-001` | derived from complete parsing |
| `REJ-GP-VER-002` | normative | challenge comparison | derived from `REQ-GP-VER-003` | derived from `REQ-GP-VER-003` |
| `REJ-GP-VER-003` | normative | terminal comparison | derived from `REQ-GP-VER-005` | derived from `REQ-GP-VER-005` |
| `OUT-GP-VER-001` | normative | accepted product instance | `REQ-GP-VER-001`, `REQ-GP-VER-003`, `REQ-GP-VER-005` | derived from the verifier requirements |
