# Cache-dependency evaluations followed the batching challenge

## Classification

- Confirmed historical Fiat-Shamir ordering bug
- Component: GKR layer-claim batching with cache dependencies
- Security character: confirmed component soundness failure in the generated
  `mem_subword_only` verifier; prover and verifier shared the bad order
- Repair started by: [`4e3142e`](https://github.com/matter-labs/zksync-airbender/commit/4e3142ead72767b21139bcaa2f2acb1da6944739)
- Fixed by: [`2df0dea`](https://github.com/matter-labs/zksync-airbender/commit/2df0dea2b68bd6ab6070484277feb9d16435c934)
- Vulnerable revision: `bf9bd04f2ac916eb8e65603cdba72f563b98351f`

## Protocol context

At the end of a sumcheck layer, the prover reveals the evaluations that become claims for the next layer. Cache relations can introduce additional dependency evaluations not present among the ordinary `new_claims`. All of these prover-controlled values are inputs to the next layer's batched claim.

The next batching coefficient must be sampled only after the complete vector is fixed. Otherwise the prover can choose the late evaluations as functions of the random coefficient used to combine them.

## Intended transcript relation

```text
ordinary_claims <- derive in canonical address order
extra_claims <- collect all cache dependencies in canonical order
complete_message = ordinary_claims || extra_claims
absorb(complete_message once)
next_batching_challenge <- squeeze(seed)
construct next-layer batched claim using that challenge
```

One absorb of the concatenation is the protocol event. Two separately framed absorbs need not produce the same seed for a fixed-block transcript construction.

## Failure

The prover absorbed `new_claims` and immediately drew `next_batching_challenge`. Only afterwards did it discover and absorb extra prover-provided evaluations required by the cache relations. The coefficient used to combine the next layer was therefore independent of part of the message it was meant to batch.

This is more serious than a CPU/GPU serialization mismatch. The same-revision
generated `mem_subword_only/sec_100` verifier followed the same order at layer
2: it committed 16 ordinary evaluations, drew `next_batching`, and only then
read and absorbed four extra cache dependencies. Those values immediately
entered the next layer's batched claim.

## Bounded accepting flow

The affected generated layer supplies four late values
`X = (x0, x1, x2, x3)`. One already-bound vector-lookup cache value constrains
them by one equation of the form:

```text
C = x0 + beta*x1 + beta^2*x2 + beta^8*x3
```

The next layer uses the already-revealed batching challenge `alpha` to retain
only one randomized combination:

```text
B = x0 + alpha*x1 + alpha^2*x2 + alpha^3*x3
```

After observing `alpha`, choose a nonzero delta vector satisfying both
homogeneous equations:

```text
delta0 + beta*delta1 + beta^2*delta2 + beta^8*delta3 = 0
delta0 + alpha*delta1 + alpha^2*delta2 + alpha^3*delta3 = 0
```

There are at most two linear constraints on four extension-field unknowns, so
a nonzero solution exists. Replacing `X` with `X + delta` preserves the cache
check and the single next-layer batched claim while making individual
evaluations false. Layer 2's final-step check covered only the 16 ordinary
values; layer 1 consumes only the batched scalar, so no later individual check
removes this freedom. Absorbing `X + delta` afterward merely determines later
challenges and cannot retroactively make `alpha` depend on it.

## Impact and fix

The verifier accepted a false local GKR layer handoff: individual evaluations
could differ from their polynomials while all checked compressed relations
remained unchanged. The review did not establish an end-to-end false public
machine statement, so the claim is component soundness rather than a broader
system exploit.

The repair sequence creates one transcript input initialized with ordinary
claims, extends it with all canonical extra evaluations, absorbs the completed
vector, and only then draws the batching challenge.

The first repair commit, `4e3142e`, left variable-name and branch-scope build
errors. `9050461d` repaired the name, and `2df0dea` moved the transition outside
the optional branch to produce the first complete compilable repair. Together
the commits show why transcript fixes must be reviewed as complete state-machine
transitions, not isolated line movements.

## Regression

- Build a layer whose only new dependency is introduced by a cache relation and assert that value appears before the first dependent squeeze.
- Mutate any extra evaluation and require `next_batching_challenge` to change.
- Compare the exact framing of `ordinary || extras`; do not accept two absorbs as automatically equivalent to one.
- Differential-test no-cache, one-cache, overlapping-cache, and several-cache layers.
- Add a negative algebraic test with inconsistent individual cache claims that could cancel only after challenge observation.

## Reproduction evidence

```sh
git diff bf9bd04f2ac916eb8e65603cdba72f563b98351f 2df0dea2b68bd6ab6070484277feb9d16435c934 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
git show bf9bd04f2ac916eb8e65603cdba72f563b98351f:verifier/src/generated/mem_subword_only/sec_100/gkr.rs
```
