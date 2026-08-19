# Timestamps were truncated through a legacy u16 parser

## Classification

- Confirmed historical proof-input/state-domain bug
- Fixed by: [`97dbacf`](https://github.com/matter-labs/zksync-airbender/commit/97dbacf8a3eec4dcb6621bc9965b1fa784efc6d5), PR [#81](https://github.com/matter-labs/zksync-airbender/pull/81)
- Vulnerable revision: `0b749ed60483e28712d89e0783552d78ea06b2cb`

## Failure

Verifier utilities reconstructed configurable timestamps through a legacy 16-bit path. Higher timestamp bits were discarded even though the memory and machine-state arguments used wider timestamp limbs.

## Impact and fix

Long executions could be interpreted under a different state history or fail to prove once timestamps exceeded the legacy range. The fix uses the full u32 representation. Audit parsers against the algebraic limb layout, especially after widening counters.

## Regression

Round-trip timestamps at `2^16-1`, `2^16`, the configured maximum, and one out-of-range value.

```sh
git diff 0b749ed60483e28712d89e0783552d78ea06b2cb 97dbacf8a3eec4dcb6621bc9965b1fa784efc6d5 -- verifier_common/src/lib.rs full_statement_verifier/src/lib.rs
```
