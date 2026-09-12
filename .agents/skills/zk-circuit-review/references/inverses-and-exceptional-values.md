# Inverses and Exceptional Field Values

## Inverse Invariant

If a witness claims:

```text
inv = 1 / x
```

then the circuit normally needs to enforce a relation equivalent to:

```text
x * inv = 1
```

or explicitly handle the `x = 0` case.

## Always Test Conceptually

```text
x = 0
x = 1
x = -1
challenge = 0
denominator = 0
max intended integer
first out-of-range integer
```

## Look For

- witness-generation-only inverses
- division assumptions
- unstated non-zero assumptions
- algebraic identities that fail at special field values
- branches introduced for zero handling
- field wraparound that violates integer semantics
- accidental equality caused by arithmetic modulo the circuit field

## Probabilistic Assumptions

If safety relies on a random challenge being non-zero or avoiding a small bad set, distinguish that probabilistic proof-system assumption from a deterministic circuit constraint.
