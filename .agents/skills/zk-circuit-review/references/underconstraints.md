# Underconstraints

## Invariant

Every prover-controlled value affecting the proved statement must be sufficiently constrained to its intended semantics.

## Look For

- allocated witnesses with few or no constraints
- witness-generation calculations not repeated algebraically
- outputs disconnected from inputs
- auxiliary witnesses treated as trusted
- variables constrained only in one direction
- prover-controlled selectors disabling required equations
- result limbs that are range checked but not linked to the operation
- state fields copied by host code but not constrained across rows

## Key Question

Can the prover choose this value differently from the honest witness generator while still satisfying all constraints?

## Vulnerable Pattern

```text
let x = witness();
let y = witness();

// witness generation computes y = x * x

enforce(y == output);
```

The circuit never proves:

```text
y == x * x
```

## Review Technique

For each witness or column:

1. find where it is allocated or populated
2. find every constraint containing it
3. determine whether those constraints establish its semantic meaning
4. attempt to assign a different value
5. trace whether later constraints indirectly fix it

## Common False Positive

A variable may appear underconstrained locally but be uniquely determined by another equality, lookup, transition relation, or table membership constraint; trace all dependencies before reporting.
