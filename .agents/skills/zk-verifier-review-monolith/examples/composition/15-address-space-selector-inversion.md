# Cached GKR memory tuples inverted the address-space tag

## Classification

- Confirmed historical compiler defect; latent and fail-closed before proof-producing circuits used the path
- Invariant: cached and uncached lowering encode identical global-memory tuples for register and RAM accesses
- Component: GKR compiler memory-permutation cache relation
- Security character: wrong address-space ownership if reachable; historical vulnerable revision did not ship a proof-producing use of the branch
- Fixed by: [`b5021bc`](https://github.com/matter-labs/zksync-airbender/commit/b5021bcd4c68d4c691a7df1ce11ce49b9222e272)
- Vulnerable revision: `725892f1727a7eaa411c8b2303cc8cecfa19410d`

## Composition context

The global memory tuple includes an address-space tag so the same numeric address cannot alias a register and RAM cell. The protocol enum encoded register space as numeric `0` and RAM as `1`.

The compiler's source expression used a Boolean predicate named `AddressSpaceIsRegister`: `Is(v)` means the predicate value `v` is one for register. Translating the predicate directly into the numeric address-space tag is therefore wrong because the two encodings use opposite polarity.

## Intended invariant

For Boolean `v`:

```text
AddressSpaceIsRegister::Is(v):
    v = 1 -> numeric tag 0 (Register)
    v = 0 -> numeric tag 1 (RAM)
    compiled relation = NOT(v)

AddressSpaceIsRegister::Not(v):
    predicate is NOT(v)
    numeric tag = v
    compiled relation = v
```

Constant, cached-dynamic, and uncached-dynamic lowering must produce the same tuple `(address_space, address, value, timestamp, ...)`.

## Failure

Cached lowering mapped `AddressSpaceIsRegister::Is(v)` to `Compiled...::Is(v)` and `Not(v)` to `Compiled...::Not(v)`. That copied the predicate polarity into a tag whose enum polarity was reversed. Register accesses became tag one (RAM), and RAM accesses became tag zero (register).

Because global memory products compress the tag together with the address, the error did not merely select the wrong local gate. It moved contributions between two semantic address spaces and could collide equal numeric addresses that should remain disjoint.

## Adversarial or failure flow

1. Use a dynamic address-space access lowered through the cache-relation path.
2. Choose `v = 1` to indicate register under the source API.
3. Compiler emits numeric tag one, which the memory protocol interprets as RAM.
4. Accumulate the mislabeled tuple into the global product.
5. Attempt to pair it against a boundary/access event from the wrong space, potentially aliasing a same-numbered RAM/register address.

At the vulnerable revision, related dynamic register/RAM lowering failed closed before proof-producing circuits reached this path, so no shipped acceptance exploit was established. The example is valuable precisely because compiler reachability must be proven before severity is assigned.

## Impact and fix

If activated, cached tuples would authenticate every dynamic register/RAM choice under the opposite address-space tag. The fix asserts the enum convention `Register == 0`, maps `Is(v)` to `Not(v)`, and maps `Not(v)` to `Is(v)`.

Boolean names and enum discriminants are different specifications. For every compiler optimization or cache relation, differential-test the full truth table against the direct expression and then establish that the path is reachable in generated verifier/prover artifacts.

## Regression

- Evaluate all four combinations of `Is`/`Not` and Boolean zero/one.
- Compare cached, uncached, and constant global-memory tuples.
- Use equal numeric addresses in register and RAM spaces and require distinct encoded tuples/products.
- Add a compile-to-proof reachability test so a latent branch cannot become live without coverage.
- Retain an assertion or typed conversion tying the compiler mapping to the enum discriminants.

## Reproduction evidence

```sh
git diff 725892f1727a7eaa411c8b2303cc8cecfa19410d b5021bcd4c68d4c691a7df1ce11ce49b9222e272 -- cs/src/gkr_compiler/utils.rs
```
