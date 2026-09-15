# LHU trap table decoded control bits from inside `funct3`

## Classification

- Confirmed historical soundness bug
- Component: memory opcode fixed table used by word/subword load-store circuits
- Bug class: packed lookup producer and table generator disagreed on bit offsets
- Fixed by: [`16e3173`](https://github.com/matter-labs/zksync-airbender/commit/16e3173f5999eeed901fc574ca6d88a317035d3b), PR [#310](https://github.com/matter-labs/zksync-airbender/pull/310)
- Vulnerable revision for reproduction: `73d69b5346b3c2350fa104a56ec4df78840cea99`

## Intended relation

The circuit packed one lookup key as:

```text
bits  0..15 : low address limb
bits 16..18 : funct3
bit      19 : is_load
bit      20 : rd_is_x0
```

The table returns address offset information plus a trap bit. The project deliberately suppresses an otherwise applicable load trap when the destination is `x0`, so both `is_load` and `rd_is_x0` are security-relevant inputs.

## Vulnerable relation

The table generator decoded:

```text
bit 17 as is_store
bit 18 as rd_is_x0
```

Both positions were already part of `funct3`; the real control bits at 19 and 20 were ignored. The table's behavior was therefore instruction-dependent in an unintended way and independent of the actual load/destination controls.

For LHU, `funct3 = 0b101`. The vulnerable decoder interpreted its middle bit as `is_store = false` and its high bit as `rd_is_x0 = true` for every LHU, regardless of the real destination register.

## Security impact

For LHU, `funct3 = 0b101` made the vulnerable generator infer `rd_is_x0 = true` regardless of the actual destination. The table could therefore suppress the alignment trap for ordinary LHU destinations, admitting a memory transition that the machine profile declares unsupported. Other load/store encodings inherited different incorrect behavior from the same overlap.

## Fix

The table generator was changed to extract `is_load` from bit 19 and `rd_is_x0` from bit 20, exactly matching both circuit producers. Its load-to-`x0` exception now uses the actual controls.

## Audit lesson

Never audit a packed lookup from its generator alone. Reconstruct the bit layout independently at every producer and consumer, including total width, field ordering, polarity, and overlapping ranges. Test each opcode whose discriminator bits can masquerade as a control flag.

## Regression test

- Exhaustively enumerate `funct3`, `is_load`, `rd_is_x0`, and the low two address bits; compare each generated table row with a small independent reference function.
- Include LHU to a nonzero destination at both aligned and misaligned offsets and assert the expected trap policy.
- Check that toggling bit 19 changes only `is_load` behavior and toggling bit 20 changes only the destination-zero exception.

## Reproduction evidence

```sh
git diff 73d69b5346b3c2350fa104a56ec4df78840cea99 16e3173f5999eeed901fc574ca6d88a317035d3b -- \
  cs/src/tables/memory_opcode_related.rs
git show 16e3173f5999eeed901fc574ca6d88a317035d3b:cs/src/machine/ops/unrolled/load_store.rs
```
