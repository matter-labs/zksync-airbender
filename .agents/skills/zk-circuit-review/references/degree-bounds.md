# Degree Bounds

## Invariant

Every declared constraint must remain within the algebraic degree supported at the point where the proof system expects to enforce it.

## Check

Track algebraic degree through:

- multiplication
- selector multiplication
- custom gates
- lookup relations
- accumulator transitions
- conditional constraints
- composed expressions

Do not infer degree from source-code complexity; compute it from the polynomial expression.

## Example

If expression `a` has degree 1 and expression `b` has degree 1, then:

```text
a * b
```

has degree 2.

Multiplying that result by another non-constant selector generally raises the degree again.

## Audit Questions

- does a nominally degree-2 gate accidentally multiply three witness-dependent terms?
- is a selector treated as a constant when it is actually a variable?
- does an optimization rewrite increase degree beyond the configured bound?
