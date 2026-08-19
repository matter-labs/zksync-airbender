# PoW threshold accepted every nonce at 32 bits

## Classification

- Confirmed latent verifier soundness and debug completeness bug
- Fixed by: [`bbf919d`](https://github.com/matter-labs/zksync-airbender/commit/bbf919d517e693827c81d0f579c74e754399292f), PR [#322](https://github.com/matter-labs/zksync-airbender/pull/322)
- Vulnerable revision: `a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0`
- Reachability: public API allowed 32; shipped configurations used at most 28

## Failure

The verifier computed `0xffffffff >> pow_bits` while permitting `pow_bits <= 32`. At 32, debug builds panicked; optimized Rust and RISC-V masked the shift to zero and produced threshold `0xffffffff`, accepting every nonce. The prover used checked shift and still performed the intended work.

## Impact and fix

Any future 32-bit phase would enforce zero grinding in the verifier. The fix single-sources a checked threshold helper shared by prover and verifier. Boundary semantics belong in the concrete budget, not only generic type/range assertions.

## Regression

Check 0, 1, 28, 31, and 32 in debug, release, and in-circuit implementations.

```sh
git diff a2d7ad19fc37e4ab90bd43ffe409269f591aa7a0 bbf919d517e693827c81d0f579c74e754399292f -- transcript/src/lib.rs transcript/src/pow.rs
```
