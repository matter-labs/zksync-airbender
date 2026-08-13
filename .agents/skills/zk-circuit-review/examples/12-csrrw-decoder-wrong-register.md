# CSRRW legality checks used the wrong register operand

## Classification

- Confirmed historical soundness bug
- Component: shift/binary/CSRRW decoder table generation
- Bug class: wrong operand in an instruction-legality predicate
- Fixed by: [`3e53f3f`](https://github.com/matter-labs/zksync-airbender/commit/3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3), PR [#329](https://github.com/matter-labs/zksync-airbender/pull/329)
- Vulnerable revision for reproduction: `bd71d8cef62bde7eb72ea22d353df0c41d551663`

## Intended relation

The custom nondeterminism CSR permits only the supported read/write operand shapes: `rs1 = x0` or `rd = x0`. Other supported custom CSRs reserve all ordinary register operands and therefore require `rs1 = rs2 = rd = x0`. Unsupported encodings must be absent from the preprocessed decoder table.

## Vulnerable relation

The decoder first forced `rs2_index = 0`, then checked:

```text
rs1_index == 0 OR rs2_index == 0
```

for the nondeterminism CSR. That predicate was always true and never constrained `rd`. For the other CSR branch it asserted only `rs1 = rs2 = 0`, omitting `rd = 0`.

## Security impact

Malformed custom-CSR encodings entered the decoder table as supported instructions. Since the table defines which bytecode transitions the execution circuit may prove, this expanded the accepted machine beyond its intended CSR contract and could attach nondeterminism or delegation behavior to unsupported register side effects.

## Fix

The nondeterminism check now tests `rs1_index == 0 || rd_index == 0`. The other CSR branch requires all three reserved indices to be zero. Failed predicates return `Err(())`, excluding the encoding from the decoder table instead of reaching assertions.

## Audit lesson

Treat decoder construction as circuit code. For each instruction format, compare every parsed bitfield with the intended operands after any normalization; a legality check can become tautological when it references a field that was just overwritten with zero.

## Regression test

- Exhaust the register-index combinations for each supported CSR and compare decoder acceptance with a small declarative policy function.
- Assert that every accepted decoder-table row has the required zero operands.
- Include valid read-only, write-only, and reserved-operand cases so tightening the table does not remove intended instructions.

## Reproduction evidence

```sh
git diff bd71d8cef62bde7eb72ea22d353df0c41d551663 3e53f3f3ac68fed1fbbcffbf28d4fcc425bd22e3 -- \
  cs/src/machine/ops/unrolled/decoder/shift_binop_csrrw.rs
```
