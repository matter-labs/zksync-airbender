# Equality and Copy Constraints

## Invariant

Two variables representing the same semantic value must be linked algebraically.

## Look For

- values copied between gadgets
- values copied between rows
- duplicated witness allocations
- state fields reconstructed independently
- outputs of one subsystem used as inputs to another
- register values read in one place and reallocated elsewhere
- lookup outputs assumed equal to arithmetic operands without an equality relation

## Typical Failure

`hash_output_a` and `hash_input_b` represent the same logical value but are allocated independently.

Without a relation equivalent to:

```text
hash_output_a == hash_input_b
```

the prover may assign them differently.

## Review Technique

Whenever the prose meaning says two values are "the same," locate the exact equality, permutation/copy constraint, transition identity, or lookup relation that enforces sameness.
