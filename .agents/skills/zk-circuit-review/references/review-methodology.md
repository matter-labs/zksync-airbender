# Circuit Review Methodology

## Contents

1. Reconstruct the statement
2. Build the scope manifest
3. Build the variable map
4. Build the semantic coverage ledger
5. Enumerate cases and attack values
6. Check completeness and soundness separately
7. Apply global assumptions precisely
8. Validate candidates adversarially
9. Record coverage honestly

## 1. Reconstruct the statement

Write one exact sentence describing the relation the circuit claims to prove. Identify the target operation set, input domain, initial state, state transition, output, and documented exclusions.

Use this evidence order:

1. formal specification and architecture documents;
2. circuit interfaces, operation/opcode definitions, and proving configuration;
3. constraint comments and construction code;
4. call sites and tests;
5. witness generation as evidence of intended behavior only.

When evidence conflicts, record the conflict. Continue with safely established semantics rather than inventing a specification.

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

## 3. Build the variable map

For every security-relevant value, record:

| Value | Source | Meaning | Intended domain | Activation domain | Enforcing relations | Destination |
|---|---|---|---|---|---|---|

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

## 5. Enumerate cases and attack values

Enumerate all intended branches and operation forms. Include real versus padding rows, first/last rows, chunk boundaries, custom operations, and preprocessing exclusions.

Try values and structures such as:

- `0`, `1`, `-1`, and field-modulus aliases;
- maximum intended limb and the first out-of-range value;
- invalid enum/opcode tags and simultaneous or absent selectors;
- zero denominators, zero challenges, and claimed inverses;
- inconsistent duplicated witnesses;
- arbitrary initial/final states;
- inactive real rows and malformed padding;
- correct local tuples with maliciously chosen fields;
- constraints computed but omitted from final aggregation.

## 6. Check completeness and soundness separately

For completeness, construct a valid intended case and determine whether the circuit admits a satisfying witness. Missing legal opcodes, impossible valid carries, or incorrect exceptional-case handling may be material completeness failures.

For soundness, construct an invalid intended case and determine whether every enforced relation can still be satisfied. Missing ranges, selector bypasses, disconnected state, and malformed lookup contributions are common causes.

Do not classify harmless redundancy or inefficiency as a material completeness failure.

## 7. Apply global assumptions precisely

Assume explicitly listed global mechanisms are consistent, then audit the local contribution under that assumption. Ask whether the candidate remains exploitable in a globally consistent execution.

For example, global RAM consistency can ensure that equal address/timestamp tuples agree, but it cannot supply a missing local constraint that should have derived an address, timestamp, type, or value from the selected operation.

Read `global-arguments-scope.md` and keep an assumption ledger.

## 8. Validate candidates adversarially

For each candidate:

1. restate the intended invariant without the proposed conclusion;
2. collect all relevant source and equations;
3. search for indirect constraints, fixed-table guarantees, configuration exclusions, and global assumptions;
4. solve or sketch the full bad assignment, not one isolated equation;
5. check that the bad case reaches an accepted output or changes the supported relation;
6. have a fresh reviewer try to close the gap;
7. demote the item if any evidence-gate condition remains unresolved.

Do not report a candidate merely because a constraint was not found quickly.

## 9. Record coverage honestly

List reviewed components, assumed invariants, and unreviewed dependencies. If time or access prevents completing the coverage ledger, say so. Do not imply that the entire circuit or proof system was audited.
