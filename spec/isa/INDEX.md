# ISA relations

> Canonical instruction and precompile relations. Proof profiles select these
> relations but do not redefine them.

- spec revision: TBD
- implementation: TBD

## Areas

| Area | Scope |
|---|---|
| [unrolled/](unrolled/) | per-family unrolled instruction relations |
| [unified/](unified/) | reduced unified instruction relations |
| [precompiles/](precompiles/) | delegated computation and fulfillment relations |

The existing `profile.md` files remain temporary inventories. Their selections move
to top-level [proof profiles](../profiles/INDEX.md) as the ISA modules are reconciled.

## Shared execution notation

- `𝓕.Execute(cycle)` abbreviates the conjunction of family `𝓕`'s canonical ISA
  relations for `cycle.text`. The execution relation supplies the timestamp-bound
  current and next PC states; the owning ISA relations constrain all emitted register,
  memory, lookup, delegation, and nondeterministic effects
