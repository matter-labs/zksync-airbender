# Verification status

**Checked** means kernel-checked claims over imported v2 native constraints
and logical matching under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [backport plan](FORMAL_VERIFICATION_PLAN.md). V3 results are source material,
not completed v2 coverage.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | Conditional ADD/ADDI/SUB/LUI/AUIPC destination and original Sail PC/register effects. Packed native masks derive the eight selector bits. The actual masked destination write is observed. Aligned PC wraparound and discarded x0 writes are included. |

| Integration | Coverage |
| --- | --- |
| V2 artifact import | All 34 quadratic and 3 linear equations, four 16-bit and eight 19-bit timestamp queries from the pinned ADD/SUB layout. Bounds/placement guards and both native zero coefficient encodings. |
| Reused foundation | Unchanged property definitions, word representation/arithmetic and pinned Sail reference/execution lemmas. Source hashes are checked. |
| Native state/port clocks | Typed physical state and three direct ports, including actual destination writes. Four-tick advancement and strict previous-write/port order follow from imported equations/queries under initial/prior clock bounds and alignment. The initialized-history layer now derives these local inputs from matching and initial boundaries. |
| Initialized logical memory | Accepted native state/memory matching, initial clock bounds/alignment and unique seed addresses construct complete Clean online consistency, per-address paths and newest preceding reads. Readonly refreshes and actual destination writes are included. Public Sail seed/initial-PC construction is checked separately below. |
| Public initial image | Actual Sail register/RAM and PC reads construct native seed tokens and initial PC at native clock four. Missing registers/bytes reject construction. Seed word/clock bounds and address uniqueness follow; no per-row values or clocks are supplied. Physical boot/profile remains separate. |
| Native decoder placement | Ten-column v2 query order, separate rd-zero flag, packed mask and actual memory/witness bank placement are imported and mechanically checked. Unsupported extra descriptor fields fail closed. Selected-profile construction and logical membership are checked below; generation/export remains separate. |
| Public decoder setup | Actual public bytes and pinned Sail decoding construct selected five-opcode rows at PCs 4*i with power-of-two capacity and the complete native-shaped minus-one tail. Missing/unsupported/effectful entries fail. Native packed-mask equations exclude padding before logical membership recovers public source evidence, zero flags and canonical PC/immediate words. Rust generation/export fidelity remains separate. |
| Initialized native word bounds | Public Sail seeds, accepted matching/clocks and complete decoder membership derive every native read, actual masked write and terminal word bound. No per-row bounds or flag answers are supplied. |
| Range tables | Native Clean static-table definitions with explicit range semantics; v2 setup-generator binding is pending. |

## Remaining work

- Bind physical Rust decoder/setup exports and expand mixed/custom programs; complete decoded row-interface assembly.
- Transport bounded latest native reads into actual subsequent Sail states; derive preprocessing, PC alignment and complete execution interfaces.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed lookups and inter-row linkage are rejected by
the initial importer rather than omitted from its local target.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all nine concrete test modules pass.
- Importer regressions: 36 checks pass.
- Axiom audit: 126 explicit roots; only propext, Classical.choice and Quot.sound.
- All eight public Review theorems (two circuit claims, four trace claims and two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 53 unchanged reused files, one native circuit artifact and thirteen native Rust sources.
- Aliased sources/destination form a nonempty accepted history. A stale alias
  read passes local constraints and is rejected by logical memory matching.
- Public Sail x1/PC reads construct the accepted alias fixture; missing register and byte data reject construction.
- Original-opcode SUB-to-x0 with nonzero source operands passes native constraints and the public Sail theorem.
- Actual ADD bytes build a padded setup and yield public Sail source evidence and native read/terminal bounds. The retained padding is rejected by native equations. A bad zero flag passes local constraints and makes an unbounded write, but lookup membership rejects it.
- U-type raw funct3, sign-extended ADDI, original-opcode x0 decoding and invalid setup capacity regressions pass.
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.
