# Attempted cache-ordering repair scoped the batching challenge inside an optional branch

## Classification

- Confirmed historical latent/build-blocking implementation defect
- Component: prover-side GKR sumcheck layer transition
- Immediate effect: the intermediate source revision did not compile because
  `next_batching_challenge` was declared inside the cache branch and used after it
- Latent protocol defect: if made compilable without moving the transition, a
  cache-free layer would omit its claim absorption and fresh batching draw
- Fixed by: [`2df0dea`](https://github.com/matter-labs/zksync-airbender/commit/2df0dea2b68bd6ab6070484277feb9d16435c934)
- Vulnerable revision: `9050461d9830eb83405b683ae526e635bc91d3a5`

## Failure

Commit `4e3142e` attempted to repair late cache-dependency evaluations by
collecting ordinary and extra next-layer claims before drawing the next batching
challenge. That commit introduced a variable-name typo. Commit `9050461d` fixed
the typo, leaving this structure:

```text
transcript_inputs = ordinary new claims

if cached_relations is nonempty:
    append extra dependency evaluations
    absorb transcript_inputs
    let next_batching_challenge = draw(seed)

... use next_batching_challenge outside the branch
```

In Rust, the branch-local `let` is not visible after the closing brace. The
function therefore failed compilation; there was no executable prover or
verifier behavior in this exact revision.

## Intended transition

Cache relations change only the optional contents of the next-layer message.
They do not decide whether the GKR layer transition occurs:

```text
transcript_inputs = ordinary new claims
if cached_relations is nonempty:
    transcript_inputs += canonical extra evaluations

absorb transcript_inputs exactly once
next_batching_challenge = draw(seed) exactly once
```

The absorb and draw must be outside the optional branch because every
nonterminal layer has ordinary next-layer claims requiring fresh batching
randomness.

## Why this is latent

The source could not produce a binary in the reviewed state, so it was not a
reachable proof-production or acceptance vulnerability. The code nevertheless
expressed a concrete protocol mistake: a naive compile-only repair that hoisted
or default-initialized the variable without moving the transcript transition
would make cache-free layers skip the transition or reuse stale randomness.

Report the immediate issue as build-blocking and preserve the protocol issue as
latent. Do not describe this commit as having executed an uninitialized or stale
challenge at runtime.

## Impact and fix

The immediate impact was build failure, not proof acceptance. The latent
protocol impact would arise only from a naive compile-only repair that leaves
the optional transcript transition intact. Commit `2df0dea` moves the combined
absorption and challenge draw after the
optional cache block, simultaneously restoring Rust scope and the unconditional
protocol transition.

### Regression properties

Regression coverage should:

- compile the affected feature/configuration;
- compare zero-cache, one-cache, and multi-cache layer event traces;
- require exactly one complete next-layer message absorption and one fresh draw
  on every nonterminal layer;
- assert every extra dependency evaluation precedes that draw; and
- avoid defaults or stale challenge state that can hide a skipped transition.

## Reproduction evidence

```sh
git diff 4e3142ead72767b21139bcaa2f2acb1da6944739 9050461d9830eb83405b683ae526e635bc91d3a5 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
git diff 9050461d9830eb83405b683ae526e635bc91d3a5 2df0dea2b68bd6ab6070484277feb9d16435c934 -- prover/src/gkr/prover/sumcheck_loop/mod.rs
```
