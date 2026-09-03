# Unified ISA: inline Blake2s relation

## Imports

- `isa/unified/operations.md`
- `isa/unified/selection.md`
- `isa/unified/integration.md`

- **`REQ-ISA-USO-001` — Core.** Enforce the complete
  [unified relation](../unified/INDEX.md).
- **`REQ-ISA-USO-002` — Blake realization.** Realize Blake2s inline using the
  tri-add and xor-rotate operations specified by `REQ-UNI-OP-002` and
  `REQ-UNI-OP-003`.
- **`REQ-ISA-USO-003` — No Blake delegation.** The resulting unified proof has no
  Blake compression or G-function fulfilment proof.
- **`REQ-ISA-USO-004` — Exclusivity.** The verifier program uses the inline
  realization, not either delegation realization.
