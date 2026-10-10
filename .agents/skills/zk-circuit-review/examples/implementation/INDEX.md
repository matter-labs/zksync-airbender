# Implementation Examples

These records concern compiler reachability, honest witness construction, or
other implementation behavior that did not weaken an exercised algebraic
circuit relation. They are retained for migration into a future implementation
review skill and excluded from blind circuit-audit scoring.

| # | Record | Fix | Category |
|---:|---|---|---|
| 1 | [Keccak padding control table](03-keccak-padding-control-table.md) | `9ae55e6` | padding witness and multiplicity generation |

Records now owned by the verifier specialists were migrated rather than copied:

- [GKR address-space selector inversion](../../../zk-verifier-composition-review/examples/15-address-space-selector-inversion.md)
- [Cached table ordering mismatch](../../../zk-stark-fri-verifier-review/examples/06-cached-table-row-order.md)
- [Native Fiat-Shamir implementation records](fiat-shamir/INDEX.md)
