# Lookups

> Decoder tables, fixed tables, range checks, timestamp checks, and their local and
> global lookup composition.

- spec revision: TBD
- implementation: TBD
- status: partial integration

| Module | Scope |
|---|---|
| [common.md](common.md) | shared table and lookup relations |
| [unrolled.md](unrolled.md) | per-family unrolled lookup layout |
| [unified.md](unified.md) | pooled unified lookup layout |

The common lookup relation is integrated. Profile-specific table inventories and the
decoder relation remain to be separated from
[machine-old/decoder.md](../machine-old/decoder.md) and related execution material.
