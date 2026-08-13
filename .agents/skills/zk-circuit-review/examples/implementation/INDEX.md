# Implementation Examples

These records concern compiler reachability, honest witness construction, or
other implementation behavior that did not weaken an exercised algebraic
circuit relation. They are retained for migration into a future implementation
review skill and excluded from blind circuit-audit scoring.

| # | Record | Fix | Category |
|---:|---|---|---|
| 1 | [GKR address-space selector inversion](01-gkr-address-space-selector-inversion.md) | `b5021bc` | latent compiler branch, fail-closed before use |
| 2 | [Cached table ordering mismatch](02-cached-table-ordering-mismatch.md) | `b6142cd` | honest multiplicity-witness placement |
| 3 | [Keccak padding control table](03-keccak-padding-control-table.md) | `9ae55e6` | padding witness and multiplicity generation |

Native transcript and Fiat-Shamir implementation records are kept under
[`fiat-shamir/`](fiat-shamir/INDEX.md).
