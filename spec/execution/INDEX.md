# Execution

> Execution binds one program to a logical machine-cycle chain, composes selected ISA
> relations, and realizes the cycles in profile-specific traces and chunks.

- spec revision: TBD
- implementation: TBD
- status: initial relation drafts

| Module | Scope | Status |
|---|---|---|
| [common.md](common.md) | program binding, logical cycles, machine-state progression, and shared activation semantics | draft with open binding gaps |
| [unrolled.md](unrolled.md) | family-specific circuit layout, chunk counts, and padding | draft with open proof-structure gap |
| [unified.md](unified.md) | in-circuit family selection, unified chunk counts, and padding | draft with open proof-structure gap |

The ISA profile owns the admitted family inventory. Execution owns authenticated
family dispatch and its physical realization. Concrete decoder-table membership and
global lookup algebra remain under [lookups](../lookups/); register and memory
argument algebra remain under [memory](../memory/).

Legacy decoder, register, PC, and continuity material remains in
[`machine-old/`](../machine-old/) as migration evidence until the open bindings in
these drafts are reconciled.
