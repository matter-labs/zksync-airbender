# Execution

> Execution composes selected ISA relations into traces, dispatches active rows, and
> fixes chunk capacities and chunk-count formulas.

- spec revision: TBD
- implementation: TBD
- status: integration stubs

| Layout | Scope |
|---|---|
| [unrolled.md](unrolled.md) | per-family unrolled dispatch and chunking |
| [unified.md](unified.md) | unified dispatch and chunking |

Shared decoder, register, PC, activation, and padding relations remain in
[`machine-old/`](../machine-old/) until they are integrated into these modules or an
explicit shared module is justified.
