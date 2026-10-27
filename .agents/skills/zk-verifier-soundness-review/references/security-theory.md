# Concrete Soundness Theory for Verifier Audits

## Contents

1. Define the experiment
2. Compose probabilities before bits
3. Fields, extensions, and challenge support
4. Algebraic tests and batching
5. Sumcheck and GKR
6. AIR, quotient, DEEP, and global arguments
7. FRI/WHIR proximity pipeline
8. Fiat-Shamir and grinding
9. Hash and commitment assumptions
10. Numerical audit procedure
11. Primary sources

## 1. Define the experiment

“Security bits” are shorthand for a bound in a specific experiment. Before
calculating, state:

- the false relation being accepted: false program execution, false polynomial
  evaluation, non-low-degree oracle, or inconsistent aggregate;
- whether the statement/setup is fixed before public parameters or chosen
  adaptively;
- whether the adversary is classical or quantum and whether the claimed result
  is in the ROM/QROM;
- the number of proof attempts, statements, chunks, recursion levels, sessions,
  and lifetime verifications covered;
- the adversary's hash/query/work budget;
- whether the target is ordinary computational soundness, knowledge soundness,
  or an IOP/PCS proximity notion.

Do not mix knowledge-error theorems with ordinary acceptance soundness without a
reduction. Do not import an interactive IOP error unchanged into a
non-interactive Fiat-Shamir proof without stating the transform assumption.

## 2. Compose probabilities before bits

Represent every failure event as a probability in one experiment. If events
`E_i` can each make a false statement accept, a conservative bound is

```text
Pr[accept false] <= sum_i Pr[E_i | all required prior good events]
```

Use a sharper composition only when the theorem establishes the required
independence or conditional structure. Convert the final probability to bits as
`floor(-log2(p_total))` in the conservative direction.

Common errors:

- adding bit counts instead of adding probabilities;
- multiplying per-round rejection probabilities while rounds are adaptive;
- treating reused challenges or query indices as independent;
- omitting union factors for layers, batches, chunks, proof classes, recursion
  levels, or many accepted proofs;
- double-counting one theorem's internal error as a separate outer term;
- combining conjectural and proven terms without labeling the result.

Maintain symbolic expressions until every count and bound has an enforced
source. Use exact/rational or interval arithmetic where practical; avoid floating
point cancellation when target errors are near `2^-100`.

## 3. Fields, extensions, and challenge support

For a Schwartz-Zippel-style event, the denominator is the size of the set from
which the relevant challenge is actually sampled, not the largest field type in
the function signature.

Check:

- base field characteristic `p`, extension degree `k`, and actual challenge
  support `S`; only use `|F_{p^k}|` when the draw is close to uniform over it;
- coefficient/limb mapping, rejection sampling or modular reduction bias,
  truncation, skipped digest words, forbidden values, and zero resampling;
- whether a nominal extension challenge is restricted to the base subfield or
  another small subset;
- whether separate extension coefficients are independently sampled or derived
  from one digest/field element;
- representation collisions that allow the same algebraic element to create
  several transcript encodings;
- characteristic wraparound in multiplicities, counts, timestamps, exponents,
  and rational-sum numerators before invoking a polynomial identity theorem.

If the challenge distribution is nonuniform, bound the bad set under that
distribution (or use min-entropy/statistical distance), rather than dividing by
the nominal field size.

## 4. Algebraic tests and batching

For an equality reduced to testing a nonzero polynomial `P(r)=0`, identify the
degree of `P` in each independently sampled coordinate. Apply the exact
univariate or multivariate theorem used by the construction. “Number of batched
items over field size” is only valid when it really bounds the combination
polynomial's degree.

For random linear combinations:

- write the combination convention exactly (`sum alpha^i f_i`, independent
  coefficients, nested batches, or a multivariate encoding);
- determine the maximum degree in each challenge after substitutions;
- check all items were fixed before the coefficient challenge;
- account for empty/singleton batches and leading/trailing zero coefficients;
- do not count correlated nested batches as independent merely because helper
  functions have different names.

For permutation, memory, and LogUp arguments, derive the collision/rational
identity polynomial from the concrete tuple encoding. Bound its degree using the
actual number of factors/rows and independently sampled key-compression
challenges. Check denominators, poles, zero factors, multiplicity ranges, and
field-characteristic bounds separately.

## 5. Sumcheck and GKR

For the classical sumcheck protocol over `n` variables with claimed individual
degree at most `d`, the familiar `n*d/|S|` expression is a conservative union
bound on round bad-challenge events only after the verifier enforces message
degree, the round sum identity, the correct initial claim, and the final
evaluation of the target polynomial. Replace `|S|` with actual challenge support.

Audit refinements:

- use the real round degree after multiplying by `eq` or other gating factors;
- use per-round degrees when they differ instead of `n*d` blindly;
- account for gate/claim batching before or within sumcheck and avoid counting
  the same randomization twice;
- establish independence or conditional freshness of layer and batching
  challenges;
- include early-termination/dimension-reduction claims and the error of exposing
  a vector rather than one terminal value;
- sum over the actual number of layer reductions and proof instances in scope;
- check the final claim is bound to the committed base layer through the PCS.

GKR soundness is not just the sum of isolated sumchecks: include wiring/`eq`
identities, randomized gate/output batches, layer handoffs, and the final PCS
opening. Cite the theorem matching the implemented batching and early-stopping
variant, or present those deviations as separately justified reductions.

## 6. AIR, quotient, DEEP, and global arguments

For AIR/STARK systems, separate:

- random composition of constraints;
- quotient identity at an out-of-domain point;
- quotient splitting/recomposition;
- DEEP/ALI batching of trace, shifted, auxiliary, and quotient evaluations;
- establishment of a proximity gap for the composition oracle;
- the subsequent FRI test.

Use actual constraint degrees, row-domain denominators, quotient degree, number
of OOD samples, and challenge support. An OOD `degree/|F|` term is not a
substitute for checking that the verifier built the correct quotient identity.

For global memory/permutation/lookup arguments, use the total accepted element
bound across all chunks and proof classes—not only one trace length. Prove that
the verifier enforces this bound and that padding/empty rows do not alter the
degree or multiplicity model.

## 7. FRI/WHIR proximity pipeline

The low-degree-test budget begins before the first query. Establish this chain:

```text
false algebraic statement
  -> reduction produces an oracle far from the target code (proximity gap)
  -> folding/compiler preserves enough distance except for stated errors
  -> query sampling detects inconsistency with stated probability
  -> Merkle/hash binding prevents changing queried values
  -> terminal degree/evaluation check closes the final oracle
```

Do not write `(1-delta)^q` until the exact theorem justifies it. Determine:

- code family, rate, domain, distance and list-decoding regime;
- whether the analysis uses unique decoding, Johnson/Guruswami-Sudan radius,
  a proximity-gap theorem, or a conjecture;
- the reduction's initial distance/gap and every round/compiler loss;
- round count, arity, fold schedule, OOD samples, terminal degree, and rate;
- whether queries are sampled with replacement, can collide, or are reused
  across rounds/batches;
- conditional error terms for adaptive oracle commitments;
- whether a batched affine space or constrained code satisfies the theorem's
  field-size/list-size hypotheses;
- the exact paper revision: WHIR's ePrint metadata notes improved compiler error
  bounds in a revision, so parameter tables must cite the analyzed version.

FRI, DEEP-FRI, and WHIR are not interchangeable formulas. WHIR is an IOP of
proximity for constrained Reed-Solomon codes and includes multilinear sumcheck
queries; audit the theorem instantiated by the implementation rather than using
a generic FRI estimate.

## 8. Fiat-Shamir and grinding

First establish the soundness/knowledge theorem for the interactive protocol and
the assumptions/loss of the Fiat-Shamir transformation. Multi-round IOPs require
more care than a three-message Sigma protocol; collision resistance alone is not
a blanket justification for the transform.

Model grinding as retries against a bound transcript prefix. Let `epsilon` be a
valid per-attempt acceptance bound and let an adversary afford at most `A`
effectively distinct attempts. A conservative classical bound is

```text
Pr[eventually accept] <= min(1, A * epsilon)
```

PoW of expected cost near `2^g` per attempt constrains `A` under a stated work
budget; it does not unconditionally change `epsilon` to `epsilon / 2^g` or “add
g bits.” State the adversary budget and protocol's security convention before
converting PoW to a margin. Account for parallelism, amortization, precomputation,
multiple grind points, nonce-space exhaustion, early-abort strategies, and any
reuse of work across related statements.

Verifier checks must bind the nonce to the exact protected transcript prefix,
enforce the threshold and nonce domain, and update/consume transcript material
consistently. A digest word selected to satisfy a leading-zero predicate has
reduced entropy and must not silently serve as an ordinary later challenge.

## 9. Hash and commitment assumptions

List separately:

- random-oracle/Fiat-Shamir modeling and query bounds;
- collision resistance for Merkle trees and transcript commitments;
- preimage or second-preimage requirements if the protocol uses them;
- digest truncation and multi-target/lifetime factors;
- reduced-round or domain-specific hash assumptions;
- encoding injectivity, domain separation, leaf/internal-node separation, tree
  shape, cap authentication, and setup-key binding.

Do not report `min(algebraic bits, hash bits)` as the whole budget when retry,
multi-target, or union factors materially reduce either term.

## 10. Numerical audit procedure

1. Extract parameters and runtime ceilings from verifier code.
2. Record exact integer values and symbolic formulas.
3. Match each formula to a primary-source theorem and version.
4. Check every theorem hypothesis against the concrete code/configuration.
5. Compute each error term conservatively with directed rounding.
6. Compose probabilities in the defined experiment.
7. Run sensitivity cases for every unresolved parameter or theorem assumption.
8. Compare against claimed bits and documented margin.
9. Recompute every in-scope security mode and prove build/deployment selects it.

## 11. Primary sources

- Thaler, *Proofs, Arguments, and Zero-Knowledge*, sumcheck/GKR chapters:
  `https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.html`
- HyperPlonk, ePrint 2022/1355:
  `https://eprint.iacr.org/2022/1355`
- DEEP-FRI, ePrint 2019/336:
  `https://eprint.iacr.org/2019/336`
- Proximity Gaps for Reed-Solomon Codes, ePrint 2020/654:
  `https://eprint.iacr.org/2020/654`
- ethSTARK documentation, ePrint 2021/582:
  `https://eprint.iacr.org/2021/582`
- WHIR, ePrint 2024/1586:
  `https://eprint.iacr.org/2024/1586`
- Fiat-Shamir Transformation of Multi-Round Interactive Proofs, ePrint
  2021/1377: `https://eprint.iacr.org/2021/1377`
- On Soundness Notions for Interactive Oracle Proofs, ePrint 2023/1256:
  `https://eprint.iacr.org/2023/1256`

Use these as routing anchors. Cite the exact theorem/section and paper revision
in an audit; an abstract or parameter table is not sufficient evidence.
