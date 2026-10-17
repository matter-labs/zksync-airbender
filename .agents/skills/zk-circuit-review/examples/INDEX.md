# Historical circuit-constraint examples

These eighteen entries are scored historical circuit bugs recovered from this
repository's Git history. They are intentionally not referenced from `SKILL.md`
while the baseline skill is being blind-tested.

Non-circuit and non-scored historical records are kept separately under
[`implementation/`](implementation/INDEX.md) and
[`hardening/`](hardening/INDEX.md).

| # | Example | Fix | Primary class | Status |
|---:|---|---|---|---|
| 1 | [Unenforced optimization context](01-unenforced-optimization-context.md) | `77e979e`, PR #212 | deferred constraints never emitted | verified |
| 2 | [Binary immediate missing from lookup](02-binary-immediate-missing-from-lookup.md) | `b5021bc` | omitted branch contribution | verified |
| 3 | [LHU trap-table packed-bit overlap](03-lhu-trap-table-packed-bit-overlap.md) | `16e3173`, PR #310 | wrong fixed-table key decoding | verified |
| 4 | [SRA enforced against wrong table](04-sra-lookup-enforced-against-wrong-table.md) | `5d73886` | witness/enforcement table mismatch | verified |
| 5 | [SRA sign-fill mask reversed](05-sra-sign-fill-mask-reversed.md) | `fa26bd6` | wrong fixed-table contents | verified |
| 6 | [Bigint SUB_NEGATE borrow sign](06-bigint-sub-negate-borrow-sign.md) | `e88874c`, PR #135 | carry/borrow recurrence sign | verified |
| 7 | [Modular multiplication Montgomery scale](07-modular-multiplication-montgomery-scale.md) | `a16b6ec`, PR #309 | field-representation mismatch | verified |
| 8 | [FMAMOD missing canonicity selector](08-fmamod-missing-canonicity-selector.md) | `a16b6ec`, PR #309 | missing opcode in aggregate | verified |
| 9 | [Modular high-limb wrong sign](09-modular-high-limb-wrong-sign.md) | `a16b6ec`, PR #309 | reduction recurrence sign | verified soundness + completeness |
| 10 | [SLTI immediate sign source](10-slti-immediate-sign-source.md) | `403b960`, PR #326 | wrong signed-comparison operand | verified |
| 11 | [Memory-tuple cache unbound](11-memory-tuple-cache-unbound.md) | `7eca15a`, PR #334 | omitted cache relation in verifier generation | verified |
| 12 | [CSRRW decoder wrong register](12-csrrw-decoder-wrong-register.md) | `3e53f3f`, PR #329 | wrong operand in legality predicate | verified |
| 13 | [MULMOD selector aliases SUBMOD](13-mulmod-selector-aliases-submod.md) | `cb51e84` | selector copy/paste omission | verified |
| 14 | [Keccak Iota final-round constant](14-keccak-iota-final-round-constant.md) | `7306247` | reachable table control omitted | verified |
| 15 | [Virtual setup evaluations unbound](15-virtual-setup-evaluations-unbound.md) | `287ba6d`, PR #282 | deterministic oracle not recomputed | verified |
| 16 | [Machine-state challenge continuity](16-machine-state-challenge-continuity.md) | `4844b40`, PR #258 | missing cross-proof challenge equality | verified |
| 17 | [Odd range-check packing](17-odd-range-check-packing-unimplemented.md) | `f6c449e` | unimplemented odd-obligation remainder | verified |
| 18 | [Bigint MEMCOPY merged range check](18-bigint-memcopy-merged-range-check.md) | `248413f7`, audit patch #1 | operation omitted from shared range-check aggregate | verified |

Each entry records the affected circuit/compiler location, intended invariant, conceptual relation failure, security impact, fix, safe regression test, and exact Git command for reproducing the historical diff.
