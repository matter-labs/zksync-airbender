# Cached GKR memory tuples inverted the address-space tag

## Classification

- Confirmed historical compiler defect; latent and fail-closed before proof-producing circuits used it
- Fixed by: [`b5021bc`](https://github.com/matter-labs/zksync-airbender/commit/b5021bcd4c68d4c691a7df1ce11ce49b9222e272)
- Vulnerable revision: `725892f1727a7eaa411c8b2303cc8cecfa19410d`

## Failure

The global memory tuple encoded register space as `0` and RAM as `1`, while `AddressSpaceIsRegister::Is(v)` made `v = 1` for registers. Cached lowering copied `v` directly for `Is` and inverted it for `Not`, exactly reversing the required numeric tag.

## Impact and fix

If reached, the cached tuple would authenticate register accesses as RAM and RAM accesses as registers. Dynamic register/RAM lowering still failed closed at the vulnerable revision, so no shipped proof used the branch. The fix explicitly checks the enum encoding and maps `Is(v)` to `1-v` and `Not(v)` to `v`.

## Regression

Evaluate all four `Is`/`Not` Boolean cases and compare cached with uncached global-memory tuples, including equal numeric addresses in the register and RAM spaces.

```sh
git diff 725892f1727a7eaa411c8b2303cc8cecfa19410d b5021bcd4c68d4c691a7df1ce11ce49b9222e272 -- cs/src/gkr_compiler/utils.rs
```
