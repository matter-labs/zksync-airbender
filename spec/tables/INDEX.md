# Tables

> Shared table construction and table semantics. Circuit modules select concrete
> tables and instantiate the lookup argument in `arguments/lookups/`.

| Module | Scope |
|---|---|
| [encoding.md](encoding.md) | class namespaces, row padding, setup construction, fixed-table admission |
| [fixed.md](fixed.md) | interface required of every fixed semantic table |
| [ranges.md](ranges.md) | verifier-derived 16-bit and timestamp-limb tables |

Table definitions do not decide which circuit uses a table, how many queries it
issues, or how its lookup outputs are packaged.

Pending individual fixed-table definitions and circuit selections are tracked in
[TODO.md](../TODO.md).
