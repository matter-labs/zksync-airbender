# Historical circuit-constraint examples

These twenty-two entries are verified, already-fixed bugs recovered from this repository's Git history. They are intentionally not referenced from `SKILL.md` while the baseline skill is being blind-tested.

| # | Example | Fix | Primary class | Status |
|---:|---|---|---|---|
| 1 | [Unenforced optimization context](01-unenforced-optimization-context.md) | `77e979e`, PR #212 | deferred constraints never emitted | verified |
| 2 | [GKR address-space selector inversion](02-gkr-address-space-selector-inversion.md) | `b5021bc` | compiler polarity/encoding mismatch | verified |
| 3 | [Binary immediate missing from lookup](03-binary-immediate-missing-from-lookup.md) | `b5021bc` | omitted branch contribution | verified |
| 4 | [LHU trap-table packed-bit overlap](04-lhu-trap-table-packed-bit-overlap.md) | `16e3173`, PR #310 | wrong fixed-table key decoding | verified |
| 5 | [SRA enforced against wrong table](05-sra-lookup-enforced-against-wrong-table.md) | `5d73886` | witness/enforcement table mismatch | verified |
| 6 | [SRA sign-fill mask reversed](06-sra-sign-fill-mask-reversed.md) | `fa26bd6` | wrong fixed-table contents | verified |
| 7 | [Bigint SUB_NEGATE borrow sign](07-bigint-sub-negate-borrow-sign.md) | `e88874c`, PR #135 | carry/borrow recurrence sign | verified |
| 8 | [Modular multiplication Montgomery scale](08-modular-multiplication-montgomery-scale.md) | `a16b6ec`, PR #309 | field-representation mismatch | verified |
| 9 | [FMAMOD missing canonicity selector](09-fmamod-missing-canonicity-selector.md) | `a16b6ec`, PR #309 | missing opcode in aggregate | verified |
| 10 | [Modular high-limb wrong sign](10-modular-high-limb-wrong-sign.md) | `a16b6ec`, PR #309 | reduction recurrence sign | verified |
| 11 | [SLTI immediate sign source](11-slti-immediate-sign-source.md) | `403b960`, PR #326 | wrong signed-comparison operand | verified |
| 12 | [Subword address decomposition](12-mem-subword-address-decomposition.md) | `7eca15a`, PR #334 | missing canonicality/alignment constraints | verified |
| 13 | [Memory-tuple cache unbound](13-memory-tuple-cache-unbound.md) | `7eca15a`, PR #334 | omitted cache relation in verifier generation | verified |
| 14 | [CSRRW decoder wrong register](14-csrrw-decoder-wrong-register.md) | `3e53f3f`, PR #329 | wrong operand in legality predicate | verified |
| 15 | [Cached table ordering mismatch](15-cached-table-ordering-mismatch.md) | `b6142cd` | physical-row/index mismatch | verified |
| 16 | [MULMOD selector aliases SUBMOD](16-mulmod-selector-aliases-submod.md) | `cb51e84` | selector copy/paste omission | verified |
| 17 | [Keccak padding control table](17-keccak-padding-control-table.md) | `9ae55e6` | disabled row produces live indices | verified |
| 18 | [Keccak Iota final-round constant](18-keccak-iota-final-round-constant.md) | `7306247` | reachable table control omitted | verified |
| 19 | [Virtual setup evaluations unbound](19-virtual-setup-evaluations-unbound.md) | `287ba6d`, PR #282 | deterministic oracle not recomputed | verified |
| 20 | [Machine-state challenge continuity](20-machine-state-challenge-continuity.md) | `4844b40`, PR #258 | missing cross-proof challenge equality | verified |
| 21 | [Odd range-check packing](21-odd-range-check-packing-unimplemented.md) | `f6c449e` | unimplemented odd-obligation remainder | verified |
| 22 | [PoW threshold full-width shift](22-pow-threshold-full-width-shift.md) | `bbf919d`, PR #322 | exceptional-value prover/verifier disagreement | verified, latent |

Each entry records the affected circuit/compiler location, intended invariant, conceptual relation failure, security impact, fix, safe regression test, and exact Git command for reproducing the historical diff.
