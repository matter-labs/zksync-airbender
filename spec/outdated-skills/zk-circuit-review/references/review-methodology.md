# Circuit Review Methodology

## Contents

1. Reconstruct the statement
2. Build the scope manifest
3. Build the variable map
4. Build the semantic coverage ledger
5. Enumerate cases and exceptional values
6. Check completeness and soundness separately
7. Apply global assumptions precisely
8. Validate candidates skeptically
9. Record coverage honestly

## 1. Reconstruct the statement

Write one exact sentence describing the relation the circuit claims to prove. Identify the target operation set, input domain, initial state, state transition, output, and documented exclusions.

Use this evidence order:

1. formal specification and architecture documents;
2. circuit interfaces, operation/opcode definitions, and proving configuration;
3. constraint comments and construction code;
4. call sites and tests;
5. witness generation as evidence of intended behavior only.

When no higher-ranked source settles a machine-semantics question, infer the
expected relation from the simulator, replayer, or transpiler. That code defines
what calling this operation is expected to produce, so it is the best available
evidence of intent — use it rather than abandoning the question.

When evidence conflicts, record the conflict. Continue with safely established
semantics rather than inventing a specification. A demonstrated disagreement
between the circuit and the reference implementation is itself a reportable
result and is never dropped. If you cannot establish which side is normative,
report it as an uncertain, specification-undefined finding: state both relations,
their exact difference, the affected operations, and the evidence that would
settle it.

## 2. Build the scope manifest

Locate every implementation layer that can affect the target relation:

- circuit constructor and constraint evaluator;
- generated or lowered constraints;
- witness columns and generators;
- fixed/preprocessed tables and setup commitments;
- selectors, challenges, accumulators, and public inputs;
- lookup, permutation, zerocheck, or argument-completion code;
- profiles or feature flags selecting circuit variants;
- tests and callers that reveal intended use.

Do not stop at the first file named after the circuit.

When several constructors, tables, generated circuits, or family variants match
the target semantics, enumerate them before narrowing scope. Trace their call
sites, profile/configuration selectors, setup inclusion, and consumers. Label a
matching implementation inactive only after this reachability search proves it;
preserve that proof in the scope manifest and revisit it if later evidence
contradicts the conclusion.

## 3. Build the variable map

For every relation-critical value, record:

| Value | Source | Meaning | Representation | Intended domain | Activation domain | Enforcing relations | Destination |
|---|---|---|---|---|---|---|---|

Sources commonly include private witnesses, public inputs, constants, fixed tables, derived expressions, selectors, lookup outputs, challenges, and accumulators.

## 4. Build the semantic coverage ledger

For every required semantic claim, identify the exact enforcing constraint, lookup, copy relation, boundary condition, or argument interface.

| Semantic claim | Cases/rows/layers | Enforcing code/equation | Assumptions | Coverage status |
|---|---|---|---|---|

Trace the full chain:

```text
specification
  -> witness/column representation
  -> local relation and activation condition
  -> aggregation/zerocheck/argument output
  -> verifier-visible or public statement
```

A correct equation that is never activated or never connected to an enforced output does not secure the statement.

For every operation form or materially different activation branch, also keep a
relation worksheet:

| Semantic value/relation | Intended expression | Honest witness/reference expression | Enforced expression | Activation condition | Status |
|---|---|---|---|---|---|

These working artifacts may be combined when that reduces repetition, provided
the fields above remain explicit and every operation form still has a visible
coverage status. Do not spend audit time reproducing the same data in several
tables.

Transcribe expressions after selector choice, helper expansion, packing, and
representation conversion. Compare them field by field or coefficient by
coefficient. The existence of a later constraint, lookup, or aggregate is not
closure unless it binds the same semantic inputs and outputs on the same active
branch.

For a deferred, merged, or selector-weighted obligation, record the activation
domain of every producer or writer of the protected value and the activation
domain of every enforcing term. Check set inclusion explicitly: every producer
domain must be covered by an enforcing domain. Do not infer coverage from a
comment, a shared destination, or the existence of an aggregate.

For multi-limb relations, normalize intended and enforced equations to the same
radix and side of equality. Record the coefficient and sign of each operand
limb, output limb, carry/borrow input and output, operation-specific adjustment,
and constant separately for the first limb, recurrent limbs, and final limb.

For every representation crossing, record both encodings and the exact
conversion equation or constant. Recover the concrete producer and consumer
contracts first rather than inferring compatibility from type names. Relevant
crossings can include raw versus decoded words, signed versus
unsigned/two's-complement values, limb radix and endianness, packed lookup/table
encodings, and canonical versus internal field forms; this list is illustrative,
not a checklist of presumed repository encodings.

## 5. Enumerate cases and exceptional values

Enumerate all intended branches and operation forms. Include real versus padding rows, first/last rows, chunk boundaries, custom operations, and preprocessing exclusions.

Do not stop after confirming one branch defect. Complete the relation worksheet
for every sibling operation and shared branch, because a nearby finding neither
proves nor disproves the remaining relations.

Try values and structures such as:

- `0`, `1`, `-1`, and field-modulus aliases;
- maximum intended limb and the first out-of-range value;
- invalid enum/opcode tags and simultaneous or absent selectors;
- zero denominators, zero challenges, and claimed inverses;
- inconsistent duplicated witnesses;
- arbitrary initial/final states;
- inactive real rows and malformed padding;
- locally well-formed tuples with inconsistent fields;
- constraints computed but omitted from final aggregation.

## 6. Check completeness and soundness separately

For completeness, construct a valid intended case and determine whether the circuit admits a satisfying witness. Missing legal opcodes, impossible valid carries, or incorrect exceptional-case handling may be material completeness failures.

For soundness, construct an invalid intended case and determine whether every enforced relation can still be satisfied. Missing ranges, selector bypasses, disconnected state, and malformed lookup contributions are common causes.

Do not classify harmless redundancy or inefficiency as a material completeness failure.

## 7. Apply global assumptions precisely

Assume explicitly listed global mechanisms are consistent, then audit the local contribution under that assumption. Ask whether the relation mismatch remains possible in a globally consistent execution.

For example, global RAM consistency can ensure that equal address/timestamp tuples agree, but it cannot supply a missing local constraint that should have derived an address, timestamp, type, or value from the selected operation.

Read `global-arguments-scope.md` and keep an assumption ledger.

## 8. Validate candidates skeptically

For each candidate:

1. restate the intended invariant without the proposed conclusion;
2. collect all relevant source and equations;
3. search for indirect constraints, fixed-table guarantees, configuration exclusions, and global assumptions;
4. solve the minimum complete bounded symbolic invalid assignment or finite trace, including every applicable selector, tuple field, direct/indirect constraint, and global-interface condition; an isolated equation or incomplete sketch is not evidence;
5. check that the bad case reaches an accepted output or changes the supported relation;
6. have a fresh reviewer try to close the gap;
7. demote the item if any evidence-gate condition remains unresolved.

Before demoting at step 7, exhaust the snapshot. If the candidate turns on what
a dependency actually does, read that dependency and resolve it; a fact you have
not yet looked up is not missing evidence. Demote only what the snapshot truly
cannot answer, and say where you searched.

Do not convert the symbolic assignment into runnable proof-generation code or an
operational reproduction procedure. Do not report a candidate merely because a
constraint was not found quickly.

Maintain a candidate disposition ledger throughout validation:

| Candidate invariant | Affected operation forms | Evidence searched | Disposition | Exact closure or remaining gap |
|---|---|---|---|---|

Use `confirmed`, `unverified`, or `closed` as the disposition.
Do not silently abandon a lead. A closed entry must name the exact relation,
reachability fact, or specification rule that closes it. Reconcile every closed
entry with later call-site, configuration, and data-flow evidence before
finalizing.

## 9. Record coverage honestly

List reviewed components, assumed invariants, and unreviewed dependencies. Include
a concise candidate disposition ledger, including closed leads whose resolution
is useful for assessing review coverage. If time or access prevents completing
the coverage ledger or relation worksheets, say so. Do not imply that the entire
circuit or proof system was audited.
