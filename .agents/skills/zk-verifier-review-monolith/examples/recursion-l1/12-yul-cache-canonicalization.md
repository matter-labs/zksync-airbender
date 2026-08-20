# Yul cached gate values were not reduced modulo the field

## Classification

- Confirmed historical EVM field-representation bug
- Boundary: generated GKR gate arithmetic → Yul scratch/cache memory → later field operations and checks
- Component: `GKR_CIRCUIT_CACHE_PTR` and generated point-evaluation expressions
- Security character: mathematically equal field elements could acquire different 256-bit machine representations
- Fixed by: [`fe19aa2`](https://github.com/matter-labs/zksync-airbender/commit/fe19aa23dce1c5bdac100756cc2a51f15f6af29e)
- Vulnerable revision: `a2e18444359b6f5c93845f9d15c9445290c68503`

## Boundary context

The EVM stores 256-bit integers, while the generated verifier reasons over the Proth field modulo `P`. A cache slot used as a field element needs a representation invariant—normally `0 <= x < P`. `addmod`/`mulmod` produce modular results, but a raw generated add/sub expression or `mstore` does not establish that invariant.

This matters when a cached value crosses into code that:

- performs raw equality/zero checks rather than modular equality;
- uses raw addition/subtraction to construct a later term;
- assumes a bounded representative when generating a negative coefficient; or
- combines cached and freshly reduced evaluation paths.

## Failure

Generated Yul stored the raw gate expression in `GKR_CIRCUIT_CACHE_PTR`. Additive or subtractive expressions could be congruent to a valid field value while lying at or above `P`. Later consumers treated the loaded word as though it were the canonical representative, while multiplication paths used modular arithmetic.

For example, a mathematical gate value `x` could be cached as `x + P`. A later modular multiplication sees `x`, but a raw comparison with `x`, or a bounded negative-term construction, sees a different machine word.

## Failure flow

1. Choose valid layer evaluations that drive a generated cached expression across the field modulus.
2. Yul stores the unreduced 256-bit result.
3. One consumer reduces implicitly through `mulmod`; another consumes or compares the raw cached word.
4. The generated verifier's paths disagree even though they are intended to evaluate the same field polynomial.
5. Depending on which predicate reaches acceptance, this yields honest-proof rejection, incorrect gate evaluation, or a fail-open opportunity in combination with a weak raw check.

The historical defect establishes representation inconsistency. A reviewer should not claim arbitrary proof acceptance without identifying the exact non-modular consumer and its control-flow path to success.

## Impact and fix

Equivalent field values could compare differently or feed inconsistent later gate evaluations. The direct fix stores `mod(gate, P)` at the cache boundary. The same change set also hardens generated negative-coefficient terms against machine-word overflow and fills missing generated constraint cases; those are related generator-soundness changes but should be reviewed as separate predicates rather than attributed solely to cache reduction.

The useful audit invariant is local and mechanical: every write into a field-typed memory region is canonical, and every equality makes clear whether it compares machine encodings or field values.

## Regression

- Drive cache expressions to `P-1`, `P`, `P+1`, just below `2P`, and any maximum reachable unreduced value.
- Compare cached and uncached Yul evaluation with Rust field evaluation for every generated gate kind.
- Assert each cache write is below `P`, not merely congruent modulo `P` after a later multiplication.
- Test raw zero/equality/revert predicates with noncanonical congruent representatives.
- Exercise negative coefficients and verify intermediate 256-bit expressions cannot wrap before modular reduction.

## Reproduction evidence

```sh
git diff a2e18444359b6f5c93845f9d15c9445290c68503 fe19aa23dce1c5bdac100756cc2a51f15f6af29e -- verifier_evm/circuit.yul verifier_evm/gkr.sol verifier_evm/parse.rs
```
