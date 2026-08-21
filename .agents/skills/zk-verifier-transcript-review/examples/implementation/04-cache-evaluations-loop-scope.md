# Cached dependency evaluations were hashed repeatedly while being collected

## Classification

- Confirmed historical prover transcript-construction bug
- Component: standard GKR layer handoff with cached relations
- Bug class: the cumulative extra-evaluation map was absorbed inside the per-relation loop
- Reachability: active prover path; the revision had no paired GKR verifier establishing a same-revision acceptance bug
- Security classification: producer completeness/parity risk only; no verifier soundness vulnerability established
- Fixed by: [`c9d8620`](https://github.com/matter-labs/zksync-airbender/commit/c9d8620d2f549781be154c6813264330b63b8a94)
- Vulnerable revision for reproduction: `e0b57de405ba1e66dbc8da572e9ac73a8d266726`

## Intended relation

A cached GKR relation can require evaluations that were not already among the
layer's ordinary claims. The prover collects those values in
`extra_evaluations_from_caching_relations`, a `BTreeMap` keyed by GKR
address.

Those extras are one logical transcript item:

```text
extras = collect every missing cache dependency
absorb(values(extras in BTreeMap order)) exactly once
proof.extra_evaluations = extras
```

This example is only about how many times that final vector is absorbed. The
separate later bug in example 10 concerns whether the extras were absorbed
before the batching challenge.

## Vulnerable relation

The absorption was inside the loop over cached relations:

```text
extras = {}

for relation in cached_relations:
    add relation's missing dependencies to extras

    if extras is nonempty:
        absorb(values(extras))       # wrong scope
```

Because `extras` was cumulative, previously collected values were hashed
again on every later iteration. If the first relation introduced `a` and the
second introduced `b`, the prover transcript was:

```text
absorb([a])
absorb([a, b])
```

The intended transcript was simply:

```text
absorb([a, b])
```

Even if the second relation introduced no new dependency, the prover absorbed
`[a]` a second time. The map order and evaluation values could therefore be
perfectly correct while the transcript event sequence was wrong.

## Security impact

No verifier soundness impact was established in this revision.

The prover's rolling seed depended on the number and decomposition of cached
relations rather than only on the final canonical extra-evaluation vector. A
verifier implementing the intended one-shot absorption derived a different seed
and rejected the otherwise honest proof when later challenges were drawn.

The affected revision did not contain a paired GKR verifier, so the confirmed
historical defect is in active proof construction. It establishes an
honest-proof/parity failure against the intended verifier transcript, not a
deployed false-acceptance vulnerability.

## Fix

The fix moved the absorption after the cached-relation loop:

```text
for relation in cached_relations:
    collect missing dependencies into extras

if extras is nonempty:
    absorb(values(extras))           # exactly once
```

The `BTreeMap` supplies canonical address order; moving the commit supplies
canonical message multiplicity.

## Audit lesson

When a transcript call appears inside an implementation loop, determine whether
the protocol defines one prover message per iteration or one message for the
completed collection. A sorted container prevents reordering but does not
prevent repeated cumulative-prefix absorption.

## Regression test

- With dependencies `a` and `b` discovered by two relations, require exactly
  one transcript event containing `[a, b]`.
- Add a second relation that introduces no dependency and require the seed to
  remain identical.
- Reorder relation discovery while preserving the final `BTreeMap` and require
  an identical transcript.
- Compare the prover event trace with the verifier's one-shot parsing of the
  serialized extra-evaluation map.

## Reproduction evidence

```sh
git diff e0b57de405ba1e66dbc8da572e9ac73a8d266726 c9d8620d2f549781be154c6813264330b63b8a94 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
