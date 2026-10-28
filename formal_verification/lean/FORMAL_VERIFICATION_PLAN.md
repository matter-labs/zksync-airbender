# Circuit formal verification plan

[Verification status](VERIFICATION_STATUS.md) owns coverage and measured evidence.
[Trust boundaries](TRUST_AND_REVIEW.md) owns external inputs and assumptions.
Start review with [public claims](Airbender/Review/README.md); supporting proof
calculations live in Proofs, imported data in Data, and parsing in Import.

## Agreed implementation scope

1. Repair assurance tooling: exact native/compiler dependency scopes on warm
   caches, prefix-query exit handling, rename-aware change selection, complete
   lookup-premise generation, native window-semantic checks and reproducible
   export comparisons. Pin the elan installer archive and checksum. Treat the
   pinned Mathlib binary cache as an explicit trusted input.
2. Make the review surface smaller without changing claims: move data and
   re-exports to Data, retain compatibility theorems outside the primary Review
   statements, move histories out of Review and centralize evidence. Preserve
   semantic models needed to understand public premises.
3. Validate affected sources and tool controls, preserve every established audit
   root, and complete environment audit/replay/negative controls under the
   existing resource limits. Do not convert interrupted or partial runs into a pass.
4. Keep CI advisory until a complete run and cold/warm/cache measurements on its
   configured runner establish feasibility. Any scheduling redesign must retain
   fresh project replay and trustworthy dependency evidence.

## Conditions to preserve

Public state/program/configuration, tracked physical RAM, modeled tables, exact
logical matching and selected complete-protocol scope remain visible. Equality
of sampled products does not imply a token permutation. Natural lookup
multiplicities remain separate from physical field counters.

The [supported-use domain](Airbender/Review/Trace/UnifiedReduced/DelegationUse.lean)
states wrapper shapes, entry safety and reference-prefix validity for bigint,
G and extended round. Invalid invocations remain excluded; lower-level witness
contracts remain explicit. G separation is retained in this domain even though
accepted complete G spans derive it from memory matching. Extended-round masks
are also premises of lower-level integrated claims, not public inputs or native
acceptance consequences. The blessed zero-low-limb rule is stated explicitly.

Keep original Sail/custom references, native IDs/imported values, BabyBear
compatibility and established audit roots. Document circuit discrepancies and
add narrow proof assumptions; changing production circuits to make proofs
succeed is outside this effort. Dependency/version churn, completeness and
unrelated parser, setup-schema or ISA changes are outside this round.

## Production machine targets

1. One public execution registry combining nondeterminism, modular operations and
   delegation calls, including missing discarded-x0 encodings and applicable
   initialization adapters. The unified combined relation is defined, but its
   native soundness and initialization adapter are open. Existing
   program-parametric source execution is narrower.
2. Compiler/setup interpretation beyond the retained four-entry decoder tables,
   with one committed production verifier program as a concrete acceptance target.
3. Derive redundant round-worker coverage from public caller coverage and native
   live-invocation matching, if a checked Lean proof establishes the implication.
4. Model and compose the blessed 361-call split Keccak path and its three native
   worker circuits for the full unsigned machine. Existing 649-call special5
   results remain conditional circuit/protocol
   coverage; [the finding](FINDINGS.md#f12--blessed-keccak-path-is-outside-current-proof-coverage)
   records this separate boundary.

## Deferred milestones

1. Universal Rust compiler correctness and complete native witness extension;
   formal decoder/preprocessor/setup-generator correspondence; cryptographic
   lookup/RAM/verifier/protocol soundness; completeness; actual large-field
   artifacts; full fetch faults, interrupts and exceptional execution.

## Verification contract

All real workers retain the shared aggregate owner and 2560 MiB footprint,
5120 MiB bounded resident, 900-second ordinary / 1800-second review limits.
Linux excludes reclaimable mapped pages from its charged-memory caps while
recording total RSS. Replay records both Lean thread and process stack limits;
a 32 MiB thread setting alone does not qualify main-thread deep recursion.

Only propext, Classical.choice and Quot.sound are standard permitted axioms.
Regenerate the dependency baseline after a successful environment audit and
review its changes. A milestone requires its actual assurance gates; source
compilation, focused replay and historical checkpoints establish their stated
scopes only.
