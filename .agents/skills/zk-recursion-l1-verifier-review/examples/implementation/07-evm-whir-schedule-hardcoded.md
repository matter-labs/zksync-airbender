# EVM WHIR generator hardcoded one round schedule

## Classification

- Implementation history: exact cross-configuration generator defect without a generated alternate verifier
- Boundary: Rust `WhirSchedule`/commitment mode → calldata flattener → generated WHIR contract
- Component: folds, queries, PoW, domains, caps, packing, and terminal polynomial geometry
- Security character: the only exercised fixture matched the hardcoded schedule; alternate configurations would be flattened/generated incorrectly
- Fixed by: [`1f8cb3c`](https://github.com/matter-labs/zksync-airbender/commit/1f8cb3cd53b45f67a1c83543b07d7c859b233120)
- Vulnerable revision: `7c8b23bf58d0c99e250f82f588fcda65bb254d8b`

## Boundary context

WHIR proof parsing is completely schedule-dependent. Per-round fold arity determines leaf width and domain updates; query count and PoW determine stream length/randomness; cap size, base LDE factor, packing, trace size, and base column counts determine Merkle geometry and final polynomial length.

The proving configuration is not fully encoded in the circuit artifact. The same `WhirSchedule` and `CommitmentMode` must drive prover, flattener, contract generation, and deployment fingerprint.

## Intended configuration contract

Derive one `WhirGenConfig` from:

```text
WhirSchedule(folds, queries, pow_bits, cap_size, base_lde_factor)
pack_log2
trace_len_log2
memory+witness width
setup width
```

Then use it for:

```text
round count/switch; query bit widths; coset bits; leaf packing;
domain generator/inverse; base caps; batching column count;
final monomial length; exact calldata flattening
```

## Failure

The WHIR calldata flattener ignored its circuit/config arguments and used fixed fold/query arrays. The Solidity template embedded one production/test `VARIANT`, one domain generator, hardcoded round switch, base column counts, and final size.

A proof generated under another valid schedule could be flattened with the wrong number/order of objects, while a contract compiled for stale constants still appeared to verify “WHIR.”

## Why excluded from verifier examples

At the vulnerable revision the committed production/test fixture used the same
fixed fold/query arrays embedded in the flattener and template. History does not
show a second schedule reaching the generated-contract test, so neither an
honest rejection nor a weaker-parameter acceptance is established. This is a
generator/configuration defect, not a latent verifier defect; a concrete emitted
alternate verifier would be required to promote it.

## Failure flow

1. Change trace size, packing, column count, cap, or WHIR round schedule.
2. Produce a proof under the new Rust configuration.
3. Flatten it using old fixed folds/queries or deploy a template with old domain geometry.
4. Parse bytes at stale boundaries and verify folds/openings under a different code/domain.
5. Reject honest proofs—or accept claims at weaker/wrong parameters if the contract identity is not tied to the intended setup/security policy.

The historical bug does not establish cross-schedule acceptance automatically; it establishes absence of a trustworthy configuration provenance chain.

## Impact and fix

Rust and EVM proof languages would drift across such a schedule change. The fix
introduces `WhirGenConfig`, validates schedule lengths/power-of-two/bounds,
derives generators and all geometry, renders a per-round switch, and passes the
same folds/queries to calldata flattening.

The deployment boundary must additionally bind the generated runtime bytecode hash to the intended schedule; correct generation cannot protect a stale deployed contract.

## Regression

- Generate at least two materially different schedules and trace/packing sizes.
- Compare calldata lengths, per-round offsets, fold/query/PoW values, generators, caps, and final monomial counts.
- Differential-test Rust and EVM acceptance for each matched configuration and reject cross-pairs.
- Assert generation fails on mismatched schedule lengths, excessive folds, invalid caps/LDE, or field two-adicity overflow.
- Record source config, generated source hash, compiler settings, and runtime bytecode hash.

## Reproduction evidence

```sh
git diff 7c8b23bf58d0c99e250f82f588fcda65bb254d8b 1f8cb3cd53b45f67a1c83543b07d7c859b233120 -- verifier_evm/src/flatten.rs verifier_evm/src/generator/whir.rs verifier_evm/src/templates/whir.sol
```
