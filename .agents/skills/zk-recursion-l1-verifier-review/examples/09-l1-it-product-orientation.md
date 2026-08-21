# GKR inits/teardowns product ratio was reversed

## Classification

- Confirmed reachable prover/composition completeness bug
- Boundary: GKR-reduced I/T pair outputs → global memory product used by unified/unrolled proof construction
- Component: `grand_product_accumulator_computed`; the fix also added a merged-mode `gkr_self_checks` closure
- Security character: active program-proof aggregation multiplied the inverse I/T factor and then required the global accumulator to equal one
- Fixed by: [`f15c643`](https://github.com/matter-labs/zksync-airbender/commit/f15c64359f852837c9ffe4fe368a62f34b6e3c89)
- Vulnerable revision: `b75be7bbecc17860dac85a6d875887a7e7fb1396`

## Boundary context

The GKR output does not expose one self-describing “memory product.” It exposes a pair whose positions have protocol meaning. The array order is:

```text
[teardown/read-side evaluation, initialization/write-side evaluation]
```

The global accumulator convention is write divided by read. Public register and PC/timestamp initialization/teardown entries are later combined under that same orientation. Array position, human name, and accumulator numerator/denominator must therefore agree across the circuit, native reduction, recursive verifier, and L1 consumer.

## Intended composition contract

For each participant, using the actual output order above:

```text
participant_ratio = init_write * inverse(teardown_read)
global_ratio *= participant_ratio
global_ratio *= verifier-injected public-state contributions
require global_ratio == 1
```

Using distinct symbolic values for the two sides is essential. Tests where both sides equal one cannot detect inversion.

## Failure

The code destructured the ordered pair as though it were `[init, teardown]`. It then multiplied the variable called `teardown` and inverted the variable called `init`. Because those names referred to the opposite array positions, the resulting factor was `teardown_read / init_write`: the inverse of the global convention.

This is a semantic interface bug, not a field-arithmetic bug. Every individual evaluation can be valid while their aggregate carries the wrong orientation.

## Failure flow

1. Circuit/GKR reduction emits a valid read-side value at index zero and write-side value at index one.
2. The L1-oriented aggregation path assigns the positions the opposite names.
3. It computes a locally well-formed ratio using those names.
4. Public machine-state factors and other chunks use the canonical write/read convention.
5. The active unified/unrolled proof builder reaches its final
   `assert_eq!(permutation_argument_accumulator, ONE)` with the participant
   factor inverted.

The active unified and unrolled proof builders multiplied
`proof.grand_product_accumulator_computed` into their global permutation
accumulator and later asserted that accumulator equals one. For nontrivial I/T
values, the inverted participant factor therefore causes honest proof generation
or composition to fail. History does not establish a verifier that shared the
swap and accepted a false memory statement, so this card does not claim
soundness.

## Impact and fix

Individually valid GKR outputs combined into the inverse global product on the
reachable program-proof path. The fix names the destructured values in their
actual order, multiplies the initialization/write value, and then multiplies the
inverse teardown/read value.

It also adds a merged-mode self-check that injects the initial and final public machine-state contributions and asserts that the resulting memory product is one. That check protects the boundary convention; it does not replace verifying each participant's claimed pair.

## Regression

- Use distinct nonunit read and write values and compare the accumulator with a direct `write/read` calculation.
- Swap the pair positions and require the closure check to fail.
- Check each circuit family, recursive layer, and EVM serialization against one named orientation contract.
- Exercise multiple chunks plus injected initial/final register and PC/timestamp events.
- Reject zero denominators before inversion rather than letting representation-specific behavior choose the result.

## Reproduction evidence

```sh
git diff b75be7bbecc17860dac85a6d875887a7e7fb1396 f15c64359f852837c9ffe4fe368a62f34b6e3c89 -- prover/src/gkr/prover/mod.rs
```
