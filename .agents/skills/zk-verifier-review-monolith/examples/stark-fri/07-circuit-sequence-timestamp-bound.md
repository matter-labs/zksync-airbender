# Circuit-sequence timestamp bound was hardcoded to u16

## Classification

- Confirmed historical large-trace completeness bug
- Fixed by: [`3f67e32`](https://github.com/matter-labs/zksync-airbender/commit/3f67e3229d3a74d1e6d5071752c22b8597e4984f), PR [#178](https://github.com/matter-labs/zksync-airbender/pull/178)
- Vulnerable revision: `9ed79293e45136eb9929dee9751fe5c181d84366`

## Failure

Cached prover data asserted the shifted circuit-sequence timestamp contribution fit `u16`, even though the protocol's configured timestamp limb width was `TIMESTAMP_COLUMNS_NUM_BITS`.

## Impact and fix

Otherwise valid batches with very high cycle counts aborted before quotient generation. The fix checks against the actual timestamp domain rather than a legacy host integer type.

## Regression

Test the largest valid circuit sequence, the first invalid one, and configurations where timestamp bits differ from 16.

```sh
git diff 9ed79293e45136eb9929dee9751fe5c181d84366 3f67e3229d3a74d1e6d5071752c22b8597e4984f -- prover/src/prover_stages/cached_data.rs
```
