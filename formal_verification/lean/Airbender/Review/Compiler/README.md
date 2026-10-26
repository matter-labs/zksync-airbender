# Compiler preservation

Review [the four principal theorems](Theorems.lean), then only the definitions
needed for the claim being assessed:

| Claim | Definitions to read |
| --- | --- |
| Every captured native arithmetic witness satisfies the original source arithmetic. | [Arithmetic semantics and the 22 configurations](Arithmetic.lean); [capture selection](../../Import/Compiler/ArithmeticInstances.lean). |
| Source arithmetic extends to the selected native arithmetic slice. | The same definitions; the selected slice is explicit. This is weaker than constructing the entire native graph. |
| Captured pooled executor rows realize Sail execution and external-read consumption. | [Pooled boundary and row selection](Pooled.lean), [row-frame contract](RowFrame.lean), [ROM domain](ROMDomain.lean). |
| Captured unified executor rows realize Sail execution. | [Unified boundary and row selection](Unified.lean), [row-frame contract](RowFrame.lean). |

The execution theorems assume canonical source framing, native arithmetic,
helper bounds, enabled authored lookup membership and active rows. The shared
row-frame definition exposes these premises; [concrete bindings](../../Import/Compiler/Rows/AddSubUncached.lean)
select the actual captured addresses and predicates for each family/cache mode.
Exact state/RAM permutations, public initial state/program/domain, configuration
and serialized inverses remain explicit. Pooled execution also assumes its
verifier boundary and independent external-read ports. Constraint validity and
decoder membership are derived.

The public program is the retained Sail-derived selection in the captured setup;
these claims do not quantify over arbitrary programs or arbitrary Rust compiler
runs. They do not discharge cryptographic matching or commitment authentication.

Artifact schemas and readers live in Import; certificate algorithms, generated
checks, witness construction, table refinements and execution calculations live
in Proofs. Those are separate implementation/import-fidelity review tasks.
[Detailed compiler evidence](../../../GKR_COMPILER_VERIFICATION.md) records the
supporting results and reproduction commands.
