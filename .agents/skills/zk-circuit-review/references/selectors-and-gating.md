# Selectors and Conditional Constraints

## Invariant

Security-critical constraints must be active under exactly the intended conditions.

## Common Form

```text
selector * constraint = 0
```

## Check

- is the selector constrained to the intended domain?
- is it boolean when treated as boolean?
- can the prover set it to zero?
- is exactly one relevant operation selector active when required?
- can multiple incompatible selectors be active simultaneously?
- is the opposite branch constrained?
- are first/last rows handled correctly?
- are padding rows distinguished safely?
- can malformed state enter an inactive branch?

## Typical Failure

```text
active * (a * b - c) = 0
```

If `active` is prover-controlled and unconstrained, setting:

```text
active = 0
```

removes the multiplication requirement.

## Completeness Check

When selectors encode opcodes or sub-operations, verify that the selector space covers exactly the intended operation set and no legal case falls through unconstrained.
