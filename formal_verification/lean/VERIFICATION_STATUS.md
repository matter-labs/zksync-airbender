# Verification status

**Checked:** the retained circuit models and conditional execution composition.
The compiler effort covers **22 captured production compilations**: eleven
families, with and without caches. Implementation enforcement gaps remain open.

## Checked coverage

| Area | Result |
| --- | --- |
| [Ordinary circuits](Airbender/Review/Circuits/README.md) | Arithmetic, branches/jumps, comparisons, shifts/bitwise and word/subword memory have reference soundness proofs. |
| [Whole execution](Airbender/Review/Trace/README.md) | Pooled and unified execution reach terminal PC/cells; actual paths include jumps and repeated-PC loops. |
| [Delegated workers](Airbender/Review/Trace/Workers/README.md) | Bigint and BLAKE2/Keccak calls compose with the CPU. Complete algorithms additionally require protocol coverage and valid memory gaps. |
| [Initialization and public inputs](Airbender/Review/Circuits/Initialization/README.md) | Native boundary products, public ROM/decoder bindings and both initialization profiles are connected to execution. |
| [GKR compiler preservation](Airbender/Review/Compiler/README.md) | All 22 captures: arithmetic, wiring, cache/lookup/RAM reductions and retained constraints. Fourteen executor adapters connect to pooled/unified Sail execution for the retained program under explicit framing, lookup and matching contracts. |

These are soundness claims under the published contracts. Compiler results
validate the captured instances; universal correctness of the Rust compiler and
cryptographic enforcement of logical matching/commitments are outside this proof.
See [Review](Airbender/Review/README.md) and [trust boundaries](TRUST_AND_REVIEW.md).

## Remaining work

1. Implementation enforcement: [F02 bigint commands](FINDINGS.md#f02--valid-bigint-operation-observations-do-not-establish-valid-calls)
   and [F04 worker RAM ports](FINDINGS.md#f04--a-valid-copy-mode-does-not-bind-native-worker-rom-to-public-bytes).
   Their composition proofs retain explicit contracts. Native G/round/Keccak
   control validity is checked after the circuit fixes.
2. Complete full independent kernel replay and the final negative-control sweep.
3. Validate remote CI, Linux controls and empty-cache reproduction on suitable
   hosts; CUDA/AVX-512 execution and a regenerated proof remain external checks.

Other implementation cases: [findings register](FINDINGS.md#linear-and-open-pr-review--15-october-2026).
Separately scoped work: [deferred milestones](FORMAL_VERIFICATION_PLAN.md#deferred-milestones).

## Validation evidence

- Earlier full suite at `5b17af422`: 1,842 modules and 176 concrete Tests pass.
  The subsequent native-control refresh has focused builds and audit reports.
- Compiler layout refactor (26 October): all 34 roots/controls, generator/layout
  checks and the exact 7,766-root axiom audit pass; standard Lean axioms only.
  Full independent replay remains incomplete.

[Detailed evidence history](VERIFICATION_HISTORY.md) ·
[Compiler scope and evidence](GKR_COMPILER_VERIFICATION.md) ·
[Reproduce checks](README.md#reproduce)
