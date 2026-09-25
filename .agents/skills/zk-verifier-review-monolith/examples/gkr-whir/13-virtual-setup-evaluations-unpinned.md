# Generated GKR verifier did not pin virtual setup polynomial evaluations

## Classification

- Confirmed historical GKR verifier component-soundness bug
- Component: layer-0 GKR claims and the immediate GKR-to-WHIR handoff
- Verifier anchor: generated `verifier/src/generated/*/sec_80/gkr.rs` layer-0 finalization and `whir.rs` initial claim
- Security character: evaluations of fixed, uncommitted virtual setup MLEs were accepted as prover-controlled claims
- Fixed by: [`287ba6d`](https://github.com/matter-labs/zksync-airbender/commit/287ba6d1086fdc5efc1d361ac779b9ad20de0bc8), PR #282
- Vulnerable revision: `b55f37d69593d0cf84b656a42eb8a3c4262d2a2a`

## Protocol context

Layer 0 contains committed memory, witness, and materialized setup oracles, but
it can also refer to fixed `VirtualSetup` polynomials whose evaluations are
computed from the public GKR point rather than opened through WHIR. Historical
variants included `RangeCheck16Bits`, `RangeCheckTimestamp`, and the low/high
inits-and-teardowns address polynomials.

These virtual polynomials are legitimate commitment optimizations only if the
verifier independently evaluates them at the final layer-0 point. They are
called virtual precisely because no PCS commitment or opening is intended or
needed. The required source of authenticity is deterministic verifier
evaluation, not a commitment. Without that evaluation, their claimed values
are unauthenticated witnesses rather than fixed setup.

## Intended claim chain

```text
sumcheck point r <- transcript-derived layer-0 challenges
committed base claims <- authenticated by WHIR openings at r
virtual setup claims <- verifier computes VirtualSetup_i(r)
layer-0 terminal gate <- evaluate using both pinned claim classes
```

No virtual setup claim should enter the terminal gate merely because it appears
in the compiled layer address list.

## Failure

The vulnerable generated verifier folded all layer-0 target evaluations into
`state.prev_claims`, including `VirtualSetup` addresses. Its WHIR initial round
then selected only the 55 committed memory/witness/setup oracle claims through
`INITIAL_WHIR_CLAIM_INDICES`. The virtual claims were intentionally absent from
the PCS batch, but the verifier had no compensating closed-form evaluation
check.

More concretely, the layer-0 verifier read 56 pairs of final-step evaluations
from the proof and passed the entire array to
`layer_0_final_step_accumulator`. That function evaluated gates such as
`LookupWithSetup` by indexing those supplied values; indices 38 and 39 were the
two virtual range/timestamp inputs. It therefore computed the gate *using
claimed virtual inputs*. It did not compute those virtual inputs from the
public evaluation point. After absorbing the pairs and drawing the last fold
challenge, it folded the same supplied pairs into `state.prev_claims`.

For example, the vulnerable generated constants placed
`VirtualSetup(RangeCheck16Bits)` and `VirtualSetup(RangeCheckTimestamp)` in
`LAYER_0_SORTED_ADDRS`, while the WHIR claim-index array skipped those entries.
The generated GKR code returned the complete `state.prev_claims`, and the WHIR
code authenticated only the indexed committed subset. No later verifier step
pinned the skipped values to their public polynomials.

## Bounded accepting freedom

At the partially fixed Sumcheck point, the prover supplies two final-variable
endpoint evaluations for each layer-0 polynomial. The terminal layer checks a
randomized gate evaluation of the form:

```text
terminal_claim = G(committed_claims(r), v_0, ..., v_k; public challenges)
```

The verifier then absorbs those endpoints, samples the last coordinate, and
folds each pair into a claim `v_i` at the full point `r`. WHIR authenticates the
committed claims but intentionally not `v_i`. Without the check
`v_i == VirtualSetup_i(r)`, the gate computation proves only consistency with
prover-chosen virtual inputs, not with the fixed range/table polynomial.
Computing `G(..., v_i, ...)` is not the same operation as computing
`VirtualSetup_i(r)`. This establishes a false local GKR claim chain; this card
does not claim that one particular public machine statement exploit was
reconstructed.

## Impact and fix

The generated verifier did not verify the compiled circuit's actual layer-0
relation whenever that relation depended on virtual setup polynomials. It
verified an existentially weakened relation in which those fixed inputs were
free.

The fix creates a canonical layer-0 layout with committed oracle columns first,
computes closed-form evaluations for every present virtual setup polynomial,
and compares them with the corresponding `state.prev_claims` before completing
the GKR-to-WHIR handoff. Range-check virtuals are evaluated from the Boolean
point and bit width; inits/teardowns low/high virtuals additionally use the
compiled word-bit parameter. Generated verifier binaries and proof fixtures
were regenerated.

## Regression

- Enumerate every `VirtualSetupPoly` variant present in the compiled artifact and require one verifier-side evaluation check.
- Mutate each virtual claim while keeping all committed WHIR openings fixed and require rejection.
- Verify the canonical layer-0 map partitions every claim into exactly one of committed/opened, verifier-computed, or separately authenticated.
- Exercise circuits containing range-check, timestamp, and inits/teardowns virtuals.
- Reject generator output when a new virtual variant has no emitted evaluator.

## Reproduction evidence

```sh
git diff b55f37d69593d0cf84b656a42eb8a3c4262d2a2a 287ba6d1086fdc5efc1d361ac779b9ad20de0bc8 -- verifier_generator/src/gkr/mod.rs verifier_generator/src/whir/rounds.rs verifier/src/generated/add_sub_lui_auipc_mop/sec_80/gkr.rs verifier/src/generated/add_sub_lui_auipc_mop/sec_80/whir.rs verifier/src/generated/add_sub_lui_auipc_mop/sec_80/constants.rs
```
