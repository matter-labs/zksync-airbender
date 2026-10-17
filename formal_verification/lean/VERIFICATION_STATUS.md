# Verification status

**Checked** means kernel-checked soundness of the imported v2 local row
constraints under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
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
| Range tables | Native Clean static-table definitions with explicit range semantics; v2 setup-generator binding is pending. |

## Remaining work

- Bind public program bytes and native decoder/setup rows; discharge local preprocessing and decoded-mask interfaces.
- Import native port/state metadata and initialized memory history; derive actual reads and operand bounds.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed lookups and inter-row linkage are rejected by
the initial importer rather than omitted from its local target.

## Validation

Current checked checkpoint:

- Library, both executables and all five concrete test modules pass.
- Importer regressions: 24 checks pass.
- Axiom audit: 35 explicit roots; only propext, Classical.choice and Quot.sound.
- Both public Review theorems have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 46 unchanged reused files, one native circuit artifact and nine native Rust sources.
- No handwritten project warnings, admitted proofs or project axioms.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.
