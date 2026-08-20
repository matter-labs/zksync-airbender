# PoW threshold accepted every nonce at 32 bits

## Classification

- Confirmed latent verifier soundness bug and debug-build completeness bug
- Component: Blake2s transcript PoW threshold shared by native and in-circuit verification
- Budget term: retry/grinding cost at the maximum supported `u32` threshold
- Reachability: public API and assertion allowed 32 bits; historical shipped configurations used at most 28
- Fixed by: [`bbf919d`](https://github.com/matter-labs/zksync-airbender/commit/bbf919d517e693827c81d0f579c74e754399292f), PR [#322](https://github.com/matter-labs/zksync-airbender/pull/322)
- Vulnerable revision: `a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0`

## Security context

The PoW verifier hashes the transcript prefix and nonce, then accepts when the first 32-bit hash word is at most a threshold. For requested work `b`, the intended inclusive threshold is:

```text
threshold(b) = floor((2^32 - 1) / 2^b)
             = u32::MAX >> b, for b < 32
threshold(32) = 0

per-attempt acceptance = (threshold + 1) / 2^32
```

At 32 bits, only a zero top word should pass. PoW is not information-theoretic soundness by itself; under the intended retry model it makes transcript resampling cost roughly `2^b` hashes per accepted attempt.

## Enforced versus claimed parameter

```text
API range: pow_bits <= 32
historical prover threshold: checked_shr(pow_bits).unwrap_or(0)
historical verifier threshold: 0xffffffff >> pow_bits
deployed maximum found in the fixing review: 28
latent failing boundary: exactly 32
```

Values `0..=31` agreed.

## Failure

The verifier used an unchecked 32-bit shift while explicitly permitting `pow_bits == 32`. In debug Rust this panicked, rejecting/aborting even honest verification. In optimized Rust, and in the RISC-V `srl` behavior used by the verifier binary, the shift amount was masked to zero and produced threshold `0xffffffff`.

Every 32-bit word is at most that threshold, so every nonce passed. The effective verifier-enforced grinding was zero bits even though the prover's checked shift still searched for a zero word and performed the intended work.

## Quantitative impact

At the boundary:

```text
intended per-attempt success = 1 / 2^32
vulnerable release verifier success = 1
intended expected work = 2^32 transcript hashes
vulnerable verifier-enforced work = 1 attempt
lost retry-cost margin = 32 bits
```

A cheating prover could select arbitrary nonces without satisfying the configured work predicate. How that changes total proof soundness depends on which challenge phase the nonce gates and the attacker's total trial budget.

Because no shipped configuration exceeded 28 bits in the historical review, this was a latent future-configuration vulnerability rather than an active deployed 32-bit break.

## Impact and fix

The legal maximum parameter had build-mode-dependent semantics and could silently remove all grinding in production. The fix adds one `Blake2sTranscript::pow_threshold` using `checked_shr(...).unwrap_or(0)` and calls it from both prover search and verifier checking.

Concrete soundness review must test arithmetic boundaries in the exact compiled targets. A range assertion such as `<= word_bits` is unsafe when the implementation language defines shifting by `word_bits` differently across debug, release, VM, or circuit backends.

## Regression

- Pin thresholds for `0`, `1`, `28`, `31`, and `32`.
- Run debug, native release, RISC-V/in-circuit, and any Solidity/Yul implementation.
- Check prover and verifier accept the same nonce set at every legal value.
- Empirically test only small `b`; use exact arithmetic rather than attempting live 32-bit grinding.
- Reject `pow_bits > 32` and document whether threshold zero means exactly 32 bits under the inclusive comparison.

## Reproduction evidence

```sh
git diff a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0 bbf919d517e693827c81d0f579c74e754399292f -- transcript/src/lib.rs transcript/src/pow.rs
```
