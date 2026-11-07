# Hardening Examples

These records document useful local invariants whose absence did not create an
independent end-to-end circuit bug under the verified global assumptions. They
are excluded from blind security-recall scoring.

| # | Record | Fix | Reason excluded |
|---:|---|---|---|
| 1 | [Subword address decomposition](01-mem-subword-address-decomposition.md) | `7eca15a`, PR #334 | bound global RAM closure already forces the active address representation |
