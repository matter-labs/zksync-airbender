# GKR Wiring and Aggregation

## Invariant

Every semantic relation computed by the named circuit must influence an output claim that the GKR/Sumcheck verifier actually enforces, with correct wiring, indexing, degree, and activation.

## Trace the layered path

For every critical base-layer value or constraint, trace:

```text
base witness input
  -> gate inputs and operation
  -> next-layer wire/index
  -> compression or batching
  -> zerocheck, lookup, memory, or public claim
  -> verifier completion
```

## Check

- gate operation matches the intended algebraic expression;
- left/right input indices and layer sizes are correct;
- no constrained output is dropped, overwritten, or routed to an unused claim;
- batching challenges are sampled after the values they bind are committed;
- random linear combinations include every required term with the intended coefficients;
- selector/multiplexer gates cover exactly the intended cases;
- claimed degrees match the supported Sumcheck degree after selector multiplication and composition;
- base-row constraints reach zerocheck or another enforcing terminal claim;
- lookup or memory outputs are exposed in the format completed by the verifier;
- generated/lowered wiring matches the source circuit description.

## Common false positive

A base-layer equation may appear to have no direct `assert_zero` call because it is accumulated and checked by a later random linear combination or zerocheck. Follow the output through every layer before reporting it as unenforced.
