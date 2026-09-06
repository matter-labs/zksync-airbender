# TRANS-SND: Transcript soundness

> The literature baseline for the Fiat-Shamir transformation, where the
> production transcript departs from it and why, the hash assumptions the targets
> actually make, and the reduction, grinding, and sampling obligations that remain
> open. This module states no composed bound; the budget lives in
> [error-budget.md](../../soundness/error-budget.md).

`*` marks a provisional assumption whose exact invocation, component, or
transcript input remains incomplete under the gaps below.

## Imports

- `protocols/transcript/verifier.md`

## Guarantee

None yet. The transformation from the public-coin interactive protocol to the
non-interactive proof is heuristic at the assessed revision; this module names
the missing reduction rather than asserting one.

## References and applicability

[Ben-Sasson, Chiesa, and Spooner, *Interactive Oracle
Proofs*](https://eprint.iacr.org/2016/116) gives the random-oracle
transformation used as the literature baseline. For statement `x`, prover root
`rt_i`, and chain state `sigma_i`, the source defines

`sigma_0 = rho_2(x)`,

`m_i = rho_1(x || sigma_(i-1))`,

`sigma_i = rho_2(rt_i || sigma_(i-1))`,

where `rho_1(y) = rho(0 || y)` and `rho_2(y) = rho(1 || y)`. Production does
not instantiate this construction verbatim. It initializes with
`H(initial)`, updates with `H(state || data)`, and exposes the resulting state
as challenge material. It therefore reverses the update preimage, omits `x`
from later challenge derivations, and merges the two prefixed oracle roles.
`GAP-TRANS-SND-001` must adapt the reduction to those differences. The source's
soundness statement has the shape

`s_sr(x, m) + O(m^2 · 2^(-λ))`,

where `m` bounds a malicious prover's oracle queries, `λ` is the digest width in
bits, and `s_sr` is state-restoration soundness at query budget `m`. The bound
is tight up to small factors. It requires the interactive protocol to be sound
against state restoration, and relates that to ordinary soundness `s` for a
`k`-round protocol by

`s(x) ≤ s_sr(x, m) ≤ binom(m, k + 1) · s(x)`

for `m ≥ k + 1`, with the matching lower-bound construction using
`floor(m/(k + 1)) · s(x) · (1 − o(1))`. Thus a many-round protocol compiles with a
loss that grows like `m^(k+1) / (k + 1)!` unless a per-round property replaces the
union bound.

[Thaler, *Proofs, Arguments, and
Zero-Knowledge*](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf)
supplies that per-round property. Round-by-round soundness requires a
well-defined state at every stage, doomed states that stay doomed under every
prover strategy, a doomed initial state for a false statement, and rejection
from a doomed final state; it is what makes a rewinding prover's advantage a
per-round escape probability rather than an exponential-in-`k` reduction cost.
Without it the only route is the constant-round reduction, which extracts an
interactive prover with success `(ε/T)^O(t)` for a `t`-round protocol and
runtime exponential in `t`; that is unusable at the round counts here. A
negligible soundness error does not substitute for the property: a sequentially
repeated protocol has negligible error and still compiles to an unsound
argument. For the source's three-message grinding example, the tight loss is a factor
of the query count, `ε_ni ≈ T · 2^(-s)`. The source discusses historical 80-bit and 100-to-128-bit
targets; the supported production mode is Sec100 only.

The same source states the binding obligation `REQ-TRANS-VER-013` enforces. The
statement must be bound before any challenge is drawn, and the concrete attack
when it is not is stated for GKR specifically: the prover produces a transcript
that passes every check but the final evaluation of the input's multilinear
extension, then solves for an input matching that evaluation in linear time.
Its generalization is what makes the setup identity, not only the input,
mandatory: any part of the statement the adversary can alter without invalidating
the transcript must be hashed.

[Canetti et al., *Fiat-Shamir: From Practice to
Theory*](https://doi.org/10.1145/3313276.3316380) gives an explicit-hash route
for multi-round GKR: round-by-round soundness, an efficiently sampleable bad
relation, and a compact correlation-intractable keyed hash family. That family
is built from fully homomorphic encryption and is conditioned on optimal
security of an LWE-based scheme against polynomial-size key-recovery attacks.
The proceedings version presents the results informally; the formal statements
are in [Canetti et al., *Fiat-Shamir From Simpler
Assumptions*](https://eprint.iacr.org/2018/1004). The current targets use fixed
concrete hashes and do not instantiate the theorem, and its hash family is far
more expensive than the interactive prover it would protect, so the route is
cited for the round-by-round property rather than as an instantiation.

None of these sources models a deliberate proof-of-work step, and none discusses
sampling a field element from hash output that is not uniform over the field.
Both are the project's own modelling steps, recorded below.

## Assumptions

- **ASM-TRANS-SND-001* — Random-oracle heuristic.** Targets below L1 use
  seven-round Blake2s; the Proth120 L1 path uses Keccak256. Each concrete hash
  is modeled as a random oracle over encoded transcript inputs. Applying the
  heuristic to reduced-round Blake2s is an explicit, non-standard assumption.

## Production deviations

Each row is a difference the reduction must cover. A fixed verifier schedule
does not by itself prove that the encodings are interchangeable.

| Deviation | Cited construction | Production behavior | Residual |
|---|---|---|---|
| merged oracle roles | `rho_1` and `rho_2` use distinct one-bit prefixes for challenge derivation and state updates | one untagged `H`; an updated state is challenge material, and other modules may select the same primitive for Merkle or recursion hashing | `GAP-TRANS-SND-001` must exclude or account for reuse of one oracle query across roles |
| update preimage order | `rho_2(data || state)` | `H(state || data)` under `REQ-TRANS-001` | `GAP-TRANS-SND-001` must give the reduction for the production order; concatenation order is not an equivalence |
| statement bound once | `x` appears in every challenge derivation | `initial` binds the statement under `REQ-TRANS-002`; later challenges derive from the chained state alone | `GAP-TRANS-SND-001` must prove that the initial binding is carried through every later state |
| reduced-round hash | a random oracle | seven of the ten Blake2s rounds below L1 | `ASM-TRANS-SND-001` |

## Error terms

The transcript contributes three quantities to the composed budget, and states
none of them as established:

- the collision term `O(m^2 · 2^(-λ))` at `λ = 256` for both hashes, against the
  query budget `m` the target admits;
- the state-restoration term `s_sr(x, m)`, which the round-by-round property is
  meant to reduce to a per-round escape probability;
- the credit each grinding stage of `REQ-TRANS-VER-008` claims against `m`.

Field sampling contributes a multiplicative factor rather than an additive term.
For BabyBear, `2^32 = 2p + r` with `r = 268435454`, so `r` residues have three
preimage words and `p − r` have two. Every event's probability under the sampled
distribution is therefore at most `3p / 2^32 = 45/32 + 3 · 2^(-32) < 1.40626`
times its probability under uniform, per drawn base-field coordinate, which is
under half a bit.

## Open obligations

- **GAP-TRANS-SND-001 — Fiat-Shamir reduction.** State the random-oracle
  reduction for the complete multi-round GKR, lookup, and WHIR transcript, and
  prove the required state-restoration or equivalent soundness property. Cover
  the untagged merged oracle roles, `state || data` update order, direct use of
  the state as challenge material, and one-time statement binding. Do not import
  either cited theorem without its additional assumptions.
- **GAP-TRANS-SND-002 — Verifier and schedule identity.** The transcript binds
  the circuit only through its absorbed setup cap, and a circuit configured with
  no setup commitment absorbs no circuit identity at all. Nothing binds the call
  schedule itself, so two verifiers with different schedules over the same
  absorbed word sequence produce the same digests. State what authenticates the
  setup identity against the verifier that consumes it, and whether the schedule
  must be bound explicitly or is fixed by that identity.
- **GAP-TRANS-SND-003 — Grinding.** No cited source models a deliberate
  proof-of-work step. Prove the claimed effect of every stage of
  `REQ-TRANS-VER-008` as a reduction of the query budget `m` in the bound above,
  and include its cost in the error budget.
- **GAP-TRANS-SND-005 — Field-sampling bias.** No cited source discusses
  sampling a challenge from hash output that is not uniform over the field.
  Instantiate every algebraic bound with the `45/32` factor derived above, or
  use uniform rejection sampling. The factor compounds per drawn coordinate, so
  the budget must count coordinates, not challenges.
- **GAP-TRANS-SND-006 — Indifferentiability of the absorber.** Every cited
  reduction models the oracle as an idealized function on arbitrary-length
  inputs. The production transcript is not that object: it drives a fixed-width
  compression directly, choosing the meaningful input length and the final-block
  flag per call, with zero-fill as the only padding. State the step from an ideal
  compression to a random oracle on variable-length input, or restate the
  reduction directly over the compression.

## Assessed deviations

- **DEV-TRANS-001 — Draw overlap.** A `squeeze` returns the current `state` as
  its first digest and recomputes the hash only for each further digest, so the
  last digest a draw returns is the state the next draw begins from. Two draws
  with no intervening `absorb` or `grind` therefore share one full digest.
  Concretely, a WHIR round's delinearization challenge is assembled from the last
  digest of that round's query-index draw; when the index draw is a single digest
  the challenge's first coordinate is also the proof-of-work-constrained word and
  its remaining coordinates are words already consumed as query-index bits.
  `REQ-TRANS-VER-005` requires a fresh, disjoint draw. `REQ-TRANS-VER-012`
  excludes the L1 path, which advances the state before every draw.

## Metadata

- profile: all targets

| ID | Authority | Activation | Depends / discharged by | Source |
|---|---|---|---|---|
| `ASM-TRANS-SND-001` | provisional | every non-interactive proof | hash boundary; `GAP-TRANS-SND-001`, `GAP-TRANS-SND-006` | random-oracle heuristic applied to the selected hashes |
| `DEV-TRANS-001` | disputed | every pair of consecutive draws below L1 | violates `REQ-TRANS-VER-005` | assessed transcript draw behavior |
| `GAP-TRANS-SND-001` | open | — | affects `ASM-TRANS-SND-001`, `REQ-TRANS-001`, `REQ-TRANS-002`; owner: human | no stated random-oracle reduction |
| `GAP-TRANS-SND-002` | open | — | affects `REQ-TRANS-004`, `REQ-TRANS-VER-013`; owner: human | no stated setup-identity or schedule binding |
| `GAP-TRANS-SND-003` | open | — | affects `REQ-TRANS-VER-005`, `REQ-TRANS-VER-008`; owner: human | grinding is unmodeled in every cited source |
| `GAP-TRANS-SND-005` | open | — | affects `REQ-TRANS-VER-010`, `OUT-TRANS-VER-001`; owner: human | biased field sampling is unmodeled in every cited source |
| `GAP-TRANS-SND-006` | open | — | affects `ASM-TRANS-SND-001`, `REQ-TRANS-VER-009`; owner: human | fixed-width absorber is not the modeled oracle |
