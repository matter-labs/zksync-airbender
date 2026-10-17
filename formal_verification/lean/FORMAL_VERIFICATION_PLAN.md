# Circuit formal verification plan

Backport the current formalization to Airbender v2 on dev while preserving its
small review surface, directory roles, pinned references and explicit trust
boundaries. This document is a snapshot of pending work; checked coverage lives
in [Verification status](VERIFICATION_STATUS.md), and accepted counterexamples
and unresolved connections live in [Findings](FINDINGS.md).

## Integrated review contract

Keep the same ownership boundaries as the source formalization:

- Review/Circuits owns selected references, artifacts, observable mappings and short public claims.
- Review/Helpers owns common properties, word representations, tables and local context.
- Review/Trace owns whole-execution and terminal-state contracts.
- Proofs owns calculations, selector recovery, native-equation checks and composition.
- Import owns the separate artifact-fidelity boundary.

Use original Clean constraint semantics and original pinned Sail standard clauses.
Reuse shared proofs unchanged when possible; record adaptations explicitly.
Derive local selectors, bounds and actual reads before promoting a row claim to
an initialized trace claim. Never hide a result or desired intermediate state in
an interface. Keep public assumptions visible and v2 findings independent.

## Continuing execution

The user authorized hourly continuation and regular commits on 17 October 2026.
The active schedule is Continue Airbender v2 formal verification backport, attached
to this backport chat. Keep working in the isolated dev-based worktree and commit
small verified milestones with Conventional Commits. Do not push without authorization.
Use the [serial bounded verification runner](scripts/check_all.py) and its
[validated watchdog](scripts/bounded_fv.py): one Lean worker, Lean memory cap
3072 MiB, total footprint at most 3072 MiB, resident at most 4096 MiB and finite
wall budgets. Confirm termination after limits and redesign instead of raising caps.
The original v3 schedule remains separate and paused.

## Pending integration work

Native direct shuffle-RAM/state metadata, ADD/SUB clock extraction and initialized
logical memory histories are checked. Accepted state/memory matching and initial
clock boundaries now derive all row/prior clock inputs, complete Clean memory
consistency and newest preceding reads. Public Sail image construction now binds
seed tokens and initial PC to actual reads, deriving initial bounds/clocks and
unique addresses. Ten-column native decoder placement/query order is checked,
including the separate zero flag. Public table construction/membership and
subsequent bound/read transport are next.

1. Import v2 fixed/setup decoder rows and bind public program construction.
   Preserve the ten-column flatten order, raw opcode funct3 bits, original x0
   opcode/operands and native minus-one padding. Connect the decoder-owned
   destination-zero flag before deriving masked-write bounds.
   Derive operand bounds and subsequent actual Sail reads through initialized
   history, using the checked public Sail seed/initial-PC constructors. The row theorem still takes
   decoded packed masks, preprocessing, bounds and Sail reads explicitly; derive
   these from public decoding and initialized history. Reuse the checked native
   clock/port descriptors and complete-path proofs.
2. Port word-memory and jump/branch/SLT alongside the first initialized ADD/SUB
   trace. Preserve v2 PC rollover behavior and verify native timestamp offsets.
3. Port unsigned mul/div, shift/binop and subword memory into the same shared
   context; retain their family-specific assumptions and supported ISA profile.
4. Rebind bigint/BLAKE/Keccak workers and callers. Retest control validity,
   unissued workers, ROM behavior and request participation on v2 before reusing
   any source finding or temporary premise.
5. Port unified execution, protocol spans, terminal boundaries, padding and
   initialization/teardown under their actual v2 argument interfaces.

Expand importer support only when a concrete circuit requires it. Nonempty
fixed-lookup sets, 8-bit columns and state linkage currently fail closed.
Do not copy unused v3 Review theorems into the v2 build.

## Deferred milestones

Faithful Rust/JSON/Lean generation, full compiled argument correspondence,
cryptographic lookup/memory/statement enforcement and completeness remain
separate milestones. Every promoted public theorem needs a nonvacuous regression,
an explicit axiom root and resolved review-guide links.
