# Unified circuit integration

## Imports

- `isa/unified/selection.md`
- `arguments/lookup/relation.md`
- `arguments/global-products/relation.md`

## Requirements

- **`REQ-UNI-INT-001` — Shared allocation.** Four executor bodies share one machine
  state, three register-or-memory access slots, and aliased scratch pools.
- **`REQ-UNI-INT-002` — Scratch isolation.** Scratch aliasing is sound only under
  [selection.md](selection.md)'s one-hot family invariant; every body must gate its
  constraints and writes by its family mask.
- **`REQ-UNI-INT-003` — Lookup pooling.** For each lookup slot, masked requests from
  all bodies are added into one width-eight generic request. No inactive body may
  contribute a nonzero term.
- **`REQ-UNI-INT-004` — Global events.** The three shared access slots and PC/state
  transition emit the local factors consumed by the global-product argument.
- **`REQ-UNI-INT-005` — Inline initialization.** The compiled unified artifact embeds
  initialization/teardown relations and exports their products and top-bit metadata.
- **`REQ-UNI-INT-006` — Single artifact.** Decoder, bodies, lookup setup, global
  products, and inline initialization are compiled into one GKR circuit artifact.
