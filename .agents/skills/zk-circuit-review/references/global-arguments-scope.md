# Local Review Under Global Assumptions

## Default boundary

Do not attempt to prove whole-system RAM/permutation soundness, cross-circuit bus equality, recursive composition, or continuity across all proving chunks during a named-circuit review.

Instead, explicitly assume each identified global mechanism is consistent according to its documented contract. Then audit whether the named circuit contributes the right locally constrained data to that mechanism.

This boundary applies only when another component completes the global
obligation. If the named target is the aggregator, recursive wrapper, or
full-statement verifier responsible for composition or continuity, that
obligation is local to the target and must be audited. For every aggregated
argument, enumerate every participating proof class and compare each challenge
field independently; equality of part of a tuple does not establish equality of
the tuple.

Analyze the empty-domain behavior of every iterated aggregation. Determine how
its references and accumulators are initialized, what downstream logic consumes
them, and whether the statement permits zero contributors. Require nonemptiness
only when the statement requires a contributor or later logic assumes a
populated reference; otherwise verify that the neutral empty case is defined and
handled consistently.

## Local obligations that remain in scope

Verify that the circuit:

- derives every tuple field from the intended local state and selected operation;
- includes the correct fields, widths, type tags, timestamps, ordering, and encoding;
- constrains selectors, execution flags, multiplicities, and dummy values;
- binds contributed values to local witnesses, state, and outputs;
- initializes and exposes local accumulators or claims correctly;
- disables contributions consistently on padding/inactive rows;
- cannot omit a required contribution or add a semantically unauthorized one;
- passes the contribution into the expected verifier-visible or aggregation output.

## Reasoning test

Ask:

```text
Assuming the global mechanism accepts exactly globally consistent contributions,
can this circuit still contribute a locally wrong but globally consistent value?
```

If yes, the missing local derivation or binding may be a circuit finding. Global consistency preserves agreement; it does not establish that the agreed value has the correct local semantics.

If the relation mismatch requires breaking the assumed global mechanism, it is not a per-circuit finding.

Do not let this assumption replace a local write-step obligation. Deterministic
initialization and teardown may justify range inheritance for the same exact
variable in a read tuple. They do not range-check a newly derived field placed
in a write/output tuple. Global tuple consistency preserves provenance; it does
not create missing provenance.

For memory-like arguments, use [memory-and-ram.md](memory-and-ram.md) to distinguish ordinary RAM histories from ROM lookup authentication, PC/timestamp state, and delegation/permutation traffic. The global assumption covers the argument's stated consistency property only; it does not prove that the circuit chose the correct relation or tuple fields.

## Multiple chunks of one circuit

Treat cross-chunk continuity, permutation closure, and aggregate equality as assumptions when they are completed outside the named chunk. Still verify each chunk's local boundary values, contribution format, activation rules, and exposed claims.

## Assumption ledger

For each dependency record:

| Assumed invariant | Local contribution | Local checks performed | Remaining system obligation |
|---|---|---|---|

Place this ledger under report scope. Do not classify a correctly wired but unreviewed global invariant as a vulnerability.
