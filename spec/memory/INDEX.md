# Memory

> Mutable-memory history relations, the global product argument that closes every
> event history, and proof-boundary initialization and teardown. ROM contents are
> lookup-owned.

- spec revision: TBD
- implementation: TBD
- status: partial integration

## Modules

| Module | Scope | Status |
|---|---|---|
| [common.md](common.md) | event schema, global product argument, RAM-history scope, and PC-state closure | draft with open inventory and accumulation gaps |
| [init-teardown-unrolled.md](init-teardown-unrolled.md) | separate unrolled initialization/teardown proof | stub |
| [init-teardown-unified.md](init-teardown-unified.md) | initialization/teardown folded into unified chunks | stub |

The product argument is one relation shared by every event class, so it is not split
by proving mode. Only the initialization/teardown boundary differs between modes: the
unrolled profile proves it in a separate circuit, the unified profile folds it into
trailing execution chunks. `REL-MEM-013` names the owner of every other event class.

## Intended contents

- register event rows, orientation, and ordering
- RAM-namespace event rows, orientation, and ordering
- address and value domains, alignment, and the `2²²` ROM-lookup/RAM dispatch boundary
- the interface to lookup-owned ROM reads and ROM-store rejection
- initialization, teardown, and final architectural memory state
- delegation event namespace and its closure

Remaining memory material stays in [machine-old/memory.md](../machine-old/memory.md)
until it is integrated here; that module still owns the legacy `ASM-MEM-001..003` and
`REQ-MEM-001..006` identifiers.

The error term of the global product argument is kept in
[soundness/memory.md](../soundness/memory.md) until it composes with the rest of the
soundness ledger.
