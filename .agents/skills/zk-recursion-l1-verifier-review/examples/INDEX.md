# Historical recursion, verifier-binary, and L1/EVM examples

These examples focus on acceptance boundaries: recursive public outputs, generated verifier identity, calldata consumption, Solidity/Yul checks, and proof-chain state. Generic transcript cases are not duplicated unless the failure is specific to the L1 handoff.

The main table contains only demonstrated soundness failures or reachable
completeness failures. [`latent/`](latent/) preserves exact defects whose affected
verifier/configuration was not yet buildable or connected to the claimed
consumer. [`implementation/`](implementation/) contains useful hardening changes
for which history does not establish false acceptance or honest-proof rejection.
Prototype/generated-contract findings name their actual test consumer and do not
claim a production deployment.

| # | Example | Fix | Primary failure |
|---:|---|---|---|
| 1 | [Generated EVM verifier omitted all LogUp identity checks](01-evm-logup-identities.md) | `bf9bd04` | runnable test-contract missing acceptance gate |
| 2 | [Generated EVM batching challenge preceded cache-dependency evaluations](02-evm-cache-evals-order.md) | `4b0d431` | runnable Rust/EVM transcript incompatibility |
| 6 | [Generated EVM verifier skipped layer 4 and used a stale output permutation](06-evm-generated-layer-order.md) | `5459c07` | wrong generated verifier semantics |
| 9 | [GKR inits/teardowns product ratio was reversed](09-l1-it-product-orientation.md) | `f15c643` | reachable global-accumulator completeness |
| 10 | [Recursive Blake leaf verifier mishandled one full block](10-recursive-blake-full-block.md) | `0e81150` | binary hash mismatch |
| 11 | [Keccak recursion boundary timestamp was one cycle late](11-keccak-recursion-timestamp.md) | `93e124e` | recursive public-state mismatch |
| 12 | [Yul cached gate values were not reduced modulo the field](12-yul-cache-canonicalization.md) | `fe19aa2` | noncanonical field cache |
| 13 | [Recursive proof output was not bound to the supplied program](13-recursion-program-binding.md) | `a2d7ad1`, PR #321 | cross-program replay |
| 14 | [Verification policy came from prover-controlled metadata](14-artifact-policy-downgrade.md) | `3e53f3f`, PR #329 | policy downgrade |
| 15 | [Unrolled recursion was not bound to the wrapped stage](15-unrolled-stage-binding.md) | `3e53f3f`, PR #329 | recursion-depth confusion |
| 16 | [Unified recursion did not enforce terminal convergence](16-unified-convergence.md) | `3e53f3f`, PR #329 | intermediate-as-final acceptance |

## Latent defects

| # | Example | Fix | Activation condition |
|---:|---|---|---|
| 4 | [Layer-0 opening list stopped at 72 instead of 113](latent/04-evm-layer0-opening-count.md) | `16a5ceb` | compile/select the unfinished Yul verifier |
| 5 | [Sumcheck failures were stored but never rejected](latent/05-yul-nonfailing-checks.md) | `4f8d993` | compile/select the pre-first-passing verifier |
| 7 | [WHIR generator hardcoded one round schedule](latent/07-evm-whir-schedule-hardcoded.md) | `1f8cb3c` | generate/flatten a non-default supported schedule |
| 8 | [Merged L1 transcript omitted terminal machine state](latent/08-l1-final-state-transcript.md) | `f15c643` | expose that state as an accepted L1 statement |

## Implementation hardening

| # | Example | Fix | Why it is not in the vulnerability corpus |
|---:|---|---|---|
| 3 | [WHIR cursor accepted trailing calldata](implementation/03-evm-trailing-calldata.md) | `4b0d431` | no false statement or honest-proof rejection established |
| 12 | [Yul cache writes were explicitly reduced](implementation/12-yul-cache-canonicalization.md) | `fe19aa2` | no old consumer distinguished congruent representatives |

Reviewers should follow every predicate through compiled/generated control flow
to all success exits and treat artifact metadata, calldata tags, and copied
recursion hashes as prover-controlled until tied to trusted policy or
authenticated verifier output.
