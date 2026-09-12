# Verifier-review historical corpus router

This coordinator does not duplicate specialist examples. Route each historical failure by its primary violated invariant:

| Specialist | Cases | Corpus focus |
|---|---:|---|
| [`zk-verifier-transcript-review`](../../zk-verifier-transcript-review/examples/INDEX.md) | 11 | absorption coverage/order, challenge derivation, optional paths, proof inputs |
| [`zk-verifier-composition-review`](../../zk-verifier-composition-review/examples/INDEX.md) | 15 | global RAM/state, chunks, padding, delegation, challenge continuity |
| [`zk-gkr-whir-verifier-review`](../../zk-gkr-whir-verifier-review/examples/INDEX.md) | 12 | Sumcheck algebra, GKR layers, MLE ordering, WHIR queries and handoff |
| [`zk-stark-fri-verifier-review`](../../zk-stark-fri-verifier-review/examples/INDEX.md) | 7 | legacy quotient/boundary generation, lookup packing, table/domain alignment |
| [`zk-verifier-soundness-review`](../../zk-verifier-soundness-review/examples/INDEX.md) | 4 | concrete PoW/security budgets and field arithmetic |
| [`zk-recursion-l1-verifier-review`](../../zk-recursion-l1-verifier-review/examples/INDEX.md) | 16 | recursive outputs, binaries, generated Solidity/Yul, calldata and L1 acceptance |
| [`zk-circuit-review`](../../zk-circuit-review/examples/INDEX.md) | 18 scored | local constraint completeness and circuit/compiler relations |

## Ownership rules

- Assign one primary owner by the first proof obligation that fails, not by the directory containing the fix.
- A single commit may fix multiple independently reproducible bugs. `c9d8620` has a transcript-scope bug and a separate WHIR batching-power bug; `4b0d431` has both ordering and exact-consumption fixes; `f15c643` has public-state binding and accumulator-orientation fixes; `3e53f3f` closes independent policy, stage-binding, and convergence gaps.
- Do not duplicate a case merely because it has downstream effects. Cross-tag it in an audit finding instead.
- Treat accepted-invalid-proof failures as soundness, rejected-honest-proof failures as completeness, and latent/configuration-only failures explicitly as such.
- The historical files are regression or evaluation material. Do not load them during a blind audit intended to test independent discovery.

## Corpus selection bar

Each included case has a concrete pre-fix semantic failure plus a closing diff, PR explanation/review, regression test, or parity witness. Generic refactors, unfinished feature additions, performance-only bugs, debug assertions, and speculative TODOs were excluded.

## Cross-cutting lessons

The parallel historical pass is fully represented in the canonical corpus. Its
three cases whose primary relation is circuit/compiler completeness remain with
`zk-circuit-review`: memory-tuple cache binding, virtual setup recomputation, and
the original machine-state continuity record. The verifier specialists link the
same boundaries without duplicating their example bodies.

The mined failures show why specialist ownership cannot become tunnel vision:

- many checks were present but degenerate—zero coefficients, hardcoded
  challenges, empty emitted branches, discarded authenticated outputs, or a
  check gated to one participant;
- material fixes occurred in generators, emitted artifacts, prover-side format
  construction, recursive binaries, and CLI/L1 callers, not only handwritten
  verifier functions;
- transcript order and protocol algebra must be reviewed together locally even
  when the complete transcript has an independent owner;
- shared-challenge continuity and acceptance-boundary binding recurred after
  earlier fixes, so both remain standing campaign ledgers.

Use one coordinator-built statement/round/freedom/artifact model, then give each
specialist a bounded slice and reconcile its handoff rows. Do not load these
historical answers during a blind rediscovery evaluation.
