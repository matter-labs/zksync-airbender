# Circuit formal verification plan

<!-- source-names: keccak_special5 -->

[Verification status](VERIFICATION_STATUS.md) separates proof coverage from
completed validation. [Trust boundaries](TRUST_AND_REVIEW.md) describes remaining
assumptions. Start with the [Review guide](Airbender/Review/README.md) for claims
and mappings; Proofs contains supporting arithmetic, native bindings and assembly.

## Remaining implementation and assurance

1. Complete full assurance for the new physical-row logical composition,
   supplied-program wrappers and explicit Airbender-platform entrypoints. The
   selected 3279-module/10-test frontend passes freshness/integrity checks without
   repairs; this binds selected manifests and issues no full assurance snapshot.
   All 14 native row compositions and public wrappers compile; execution/public modules pass selected-module replay at a
   32 MiB Lean thread stack. Physical arithmetic/active rows and
   exact tuple matching now replace canonical framing and supplied helper/authored
   validity in those APIs. Actual native field/leaf operands are transported to
   source operands using arithmetic, primitive/group coverage and setup bindings.
   Preserve the exact-permutation RAM boundary and the explicit final
   compressed/sampled-to-exact lookup abstraction. Natural lookup multiplicities
   remain independent of physical counters, and supplied programs
   must have decoder tables equal to the retained capture's tables; arbitrary new
   setups still need interpretation evidence.
2. Finish declaration-origin and standard-axiom dependency auditing with reviewed
   baseline dispositions. Direct axiom reports are smoke tests. Run independent
   kernel replay and false-proof controls over the current compiled inventory.
3. Verify native evidence and both cached/uncached compiler provenance, all concrete
   Tests and executables, importer regressions, and review/reference boundaries.
4. Measure Linux resource/process controls, the finite replay stack and cold-cache
   reproduction. FV CI is temporarily advisory on relevant changes; selectively
   required checks follow a complete Linux pass.

The legacy HashABI helper/trace dependency is resolved: reusable round and special5
controller definitions now live in circuit-level protocol modules, with their
names and bodies preserved. The layer check and focused consumer build pass.
Linux guard and compilation-pool controls pass (49 tests); full Linux Lean and
cold-cache gates remain distinct from those process controls.
The full frontend also exposed late imports in the audit entrypoint. They now
precede all commands, with all 908 imports and 12409 audit roots preserved in
order; the repaired entrypoint compiles. Full source/runtime closure, environment
auditing and transitive replay remain pending.

Program-parametric actual-path execution and complete native-span composition
already exist, including branches, jumps and loops under their stated contracts.
Canonical endpoint closure, inactive-padding closure, initialization token products
and native participation must be assessed at their published logical scope rather
than reported as wholly missing. Dated regressions and intermediate interfaces
remain in the [historical record](TRUST_AND_REVIEW_HISTORY.md).

## Conditions and findings to preserve

The source/trace proof path is public initialization, preserved write bounds and
latest-write reads, then native decoding/constraints and reference execution.
Public state/program/configuration, modeled tables, exact logical matching and
selected complete-protocol scope remain visible. Equality of sampled products
does not deterministically imply token-multiset equality or cryptographic soundness.

[F02 bigint commands](FINDINGS.md#f02--valid-bigint-operation-observations-do-not-establish-valid-calls),
[F04 worker RAM ports](FINDINGS.md#f04--a-valid-copy-mode-does-not-bind-native-worker-rom-to-public-bytes)
and [F11 hash witness contracts](FINDINGS.md#f11--hash-witness-contracts-remain-unenforced)
record native behavior outside the supported delegation-use domain. The public
[ValidDelegationUse](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean) contract
states wrapper shapes, entry safety and reference-prefix argument validity.
Preserve the original conditional worker APIs, and derive their premises in the
supported-use entrypoint through exact native prefixes. G pointer separation
remains a program obligation until the full-bundle memory argument is proved.
Document new circuit discrepancies and add only narrow explicit assumptions;
circuit changes to make proofs succeed are outside this effort.

Preserve the pinned Sail clauses/custom references, imported values/native IDs,
BabyBear compatibility claims and retained audit roots. Serialized coefficients
remain distinct from generic capacity arithmetic. Completeness, proof-style
changes, dependency churn, parser/setup-schema redesign, ISA expansion and standard
boot-ROM-data copying remain outside scope.

## Deferred milestones

These require separately scoped work:

1. Universal correctness of the Rust compiler and witness extension to the complete
   emitted graph. Current captured base-field arithmetic preservation and standalone
   wiring/lookup/RAM reductions are narrower proved results.
2. Formal Rust decoder/preprocessing and setup-generator correspondence beyond
   checked artifact export/import and provenance.
3. Cryptographic lookup/memory-argument soundness, verifier implementation refinement
   and protocol soundness.
4. Completeness for the declared circuit relations.
5. Actual Proth120/large-field artifacts and coefficients; generic arithmetic alone
   does not establish a native large-field import.
6. Full fetch faults, interrupts and exceptional execution.
7. The blessed 361-call Keccak wrapper: model column-parity, theta/rho and chi5,
   prove their composition, and check caller/CSR/setup integration. Current
   results cover only the distinct 649-call `keccak_special5` protocol; the
   inspected unified setup also omits the split CSRs. The agreed scope keeps
   special5 as conditional circuit/protocol coverage and defers this work.
   [F12](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage)
   records the evidence and the supported-use contract boundary.

## Verification and completion

[Reproduction](README.md#reproduce) describes ordinary checking, provenance,
environment dependency auditing and independent replay. All workers share one
aggregate owner and retain 2560 MiB footprint, 5120 MiB bounded resident and
900-second normal/1800-second review budgets. Linux charged-memory caps exclude
mapped file pages, with total RSS retained as telemetry. Replay uses an explicit
32 MiB Lean thread stack recorded in its identity on all hosts. Linux additionally
sets a 32 MiB process stack limit; Darwin retains and records its inherited process
limit because its OS rejects changes. The default requires full-proof validation;
the reported deep-recursion failures are not yet established as fixed. Peak memory,
runtime and stack measurements belong with the corresponding evidence, not an
inferred pass claim.

Standard permitted axioms are propext, Classical.choice and Quot.sound. A
milestone is complete only when its current statements and required assurance
gates pass; focused builds and historical reports do not establish that result.
