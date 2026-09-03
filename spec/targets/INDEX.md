# Targets

A target selects one concrete proving and verification configuration. It references
canonical relations; it does not restate them.

`Sec100` is the only supported security mode. There is no current 80-bit target.

## Proven machines

The main program uses the full unrolled ISA. Reduced recursion uses exactly three
unified proven machines:

- [Blake2s compression delegation](../isa/unified-blake-compression/INDEX.md);
- [Blake2s G-function delegation](../isa/unified-blake-g-function/INDEX.md);
- [inline Blake2s special operations](../isa/unified-special-opcodes/INDEX.md).

No fourth unified ISA profile is supported. The unrolled base-layer and recursion-layer
FSV programs support compression and G-function modes; special operations are unified
only. A unified base-layer entrypoint exists, but it is not a recursion-pipeline target.
Target support is determined by the proving and verification configuration, not by
whether a generated binary is checked into the repository.

| Target | Scope |
|---|---|
| [unrolled-base-sec100.md](unrolled-base-sec100.md) | unrolled base proof and host artifact verification |
| [unrolled-recursion-sec100.md](unrolled-recursion-sec100.md) | optional unrolled recursion stage and unified bridge |
| [unified-recursion-sec100-blake-compression.md](unified-recursion-sec100-blake-compression.md) | unified recursion with Blake2s compression delegation |
| [unified-recursion-sec100-blake-g-function.md](unified-recursion-sec100-blake-g-function.md) | unified recursion with Blake2s G-function delegation |
| [unified-recursion-sec100-special-opcodes.md](unified-recursion-sec100-special-opcodes.md) | unified recursion with inline Blake2s operations |
| [unified-recursion-sec100-l1-feeder.md](unified-recursion-sec100-l1-feeder.md) | high-LDE final BabyBear layer consumed by L1 |
| [l1-proth120.md](l1-proth120.md) | packed Proth120 L1 proof |

Concrete GKR/WHIR schedules are in [parameters.md](parameters.md).
