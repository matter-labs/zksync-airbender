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
| Initialized logical memory | Accepted native state/memory matching, initial clock bounds/alignment and unique seed addresses construct complete Clean online consistency, per-address paths and newest preceding reads. Readonly refreshes and actual destination writes are included. Public Sail image binding remains pending. |
| Range tables | Native Clean static-table definitions with explicit range semantics; v2 setup-generator binding is pending. |

## Remaining work

- Bind public program bytes and native decoder/setup rows; discharge local preprocessing and decoded-mask interfaces.
- Bind initialized logical memory to public Sail state; derive actual Sail reads and operand bounds.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed lookups and inter-row linkage are rejected by
the initial importer rather than omitted from its local target.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all seven concrete test modules pass.
- Importer regressions: 30 checks pass.
- Axiom audit: 67 explicit roots; only propext, Classical.choice and Quot.sound.
- All five public Review theorems (two circuit claims, one initialized-memory claim and two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 51 unchanged reused files, one native circuit artifact and eleven native Rust sources.
- Aliased sources/destination form a nonempty accepted history. A stale alias
  read passes local constraints and is rejected by logical memory matching.
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.
