# Legacy AIR, DEEP-ALI, and FRI Verifier Review

## Contents

1. Airbender legacy profile
2. AIR and quotient construction
3. Transcript phases
4. DEEP batching
5. FRI verification
6. Boundaries and row exceptions
7. Legacy implementation checklist
8. Migration and version identification

## 1. Airbender legacy profile

Historical Airbender releases used an AIR/STARK architecture. Do not apply current GKR assumptions to them. Fingerprint the tag and inspect its own `verifier/`, `verifier_common/`, `verifier_generator/`, `full_statement_verifier/`, `transcript/`, and staged prover files.

The broad historical design was:

```text
execution/setup/witness/memory trace polynomials
  -> commitments
  -> lookup/memory auxiliary polynomials and commitments
  -> random batching of AIR constraints
  -> quotient polynomial and degree splitting
  -> out-of-domain evaluations / DEEP-ALI batch
  -> FRI folding of one batched polynomial
  -> query authentication against all relevant Merkle oracles
```

Constraints were generally limited to degree two, but selectors, boundary denominators, quotienting, and batching affect actual quotient degree. Older variants had special first/last-row domains and, in still older designs, previous/next-cycle openings. Recover the exact version rather than generalizing this profile.

## 2. AIR and quotient construction

Let trace columns interpolate polynomials over a trace domain `H`. AIR constraints `C_j` must vanish on their intended row domains. The verifier usually combines them with random coefficients and divides by vanishing polynomials:

```text
Q(x) = sum_j alpha_j * C_j(x) / Z_j(x)
```

where `Z_j` encodes the rows on which constraint `j` must vanish. The resulting quotient may be split into degree-bounded parts for commitment/opening.

Audit:

- exact constraint groups and random coefficients;
- whether all constraints are present once in the generated quotient evaluator;
- selector and boundary-domain denominators;
- degree calculation and number/order of quotient parts;
- evaluation/recomposition of split quotient parts;
- trace arguments at `z`, `z*omega`, or other shifted points;
- setup, witness, memory, auxiliary, and quotient column offsets;
- consistency between circuit layout, generated quotient code, and verifier constants.

The verifier must check the quotient identity at the sampled out-of-domain point. Merely opening quotient and trace values does not enforce their algebraic relation.

## 3. Transcript phases

A common phase structure is:

1. Bind public statement and setup/fixed commitments.
2. Bind witness and memory trace commitments.
3. Draw memory/permutation and lookup challenges only after the columns they randomize are committed.
4. Construct and bind auxiliary/grand-product/lookup commitments.
5. Draw constraint-batching challenges.
6. Construct and bind quotient commitments.
7. Draw out-of-domain evaluation point(s).
8. Read, bind, and verify all claimed evaluations and quotient identity.
9. Draw DEEP batching challenge.
10. Commit/fold FRI oracles, absorbing each before its next fold challenge.
11. Bind final polynomial/terminal values and PoW before query derivation.
12. Derive query indices and authenticate/open every batched source oracle.

Exact versions may draw some challenges at different points for justified constructions. Reconstruct the interactive protocol and prove every deviation sound. The classic Frozen Heart failure in this setting is drawing a permutation/lookup challenge before all witness or multiplicity columns that use it are committed.

## 4. DEEP batching

DEEP-ALI/DEEP-FRI samples outside the original evaluation domain and uses claimed evaluations to improve distance/soundness. A typical deep composition combines terms of the shape:

```text
(f(x) - f(z)) / (x - z)
```

and shifted-point analogues such as `z*omega`, with random coefficients into one polynomial subsequently tested by FRI.

Audit:

- `z` is outside all forbidden domains and sampled after source commitments;
- every claimed `f(z)`/`f(z*omega)` is bound before the DEEP batching challenge;
- source polynomial order, signs, point type, and alpha powers match verifier reconstruction;
- setup, witness, memory, auxiliary, and quotient terms are all included;
- the quotient identity is checked using the same evaluations;
- denominators are nonzero or exceptional values are handled;
- shifted openings correspond to the correct transition direction;
- the final batched polynomial's claimed value and degree follow from the source degrees;
- quotient splitting/recomposition does not leave a high-degree component unbound.

The verifier must authenticate queried source values and verify that their DEEP combination matches queried FRI values. A low-degree FRI oracle alone is not proof that it was formed from the committed trace.

## 5. FRI verification

At each FRI round:

1. The current oracle is already committed.
2. The verifier samples a fresh folding challenge.
3. The prover folds to a smaller oracle and commits to it, unless the terminal representation is sent directly.
4. The next challenge depends on that new commitment.

After all commitments and terminal data are fixed, the verifier derives query indices, authenticates corresponding leaves, checks fold consistency round-by-round, and verifies the final low-degree polynomial.

Audit:

- fold factor and formula for every schedule step;
- coset/domain generator and inverse twiddles;
- bit reversal and leaf packing;
- challenge powers for fold-by-2/4/8 or variable folds;
- cap size and early stopping at cap/leaf boundaries;
- direct terminal leaves versus committed terminal oracle;
- final monomial coefficient count and degree;
- transcript absorption of each cap and terminal value;
- PoW placement immediately before the randomness it hardens;
- query count, uniqueness assumptions, and derivation bias;
- authentication of every setup/witness/memory/auxiliary/quotient/FRI leaf used in the check;
- consistent query index projection across successively smaller domains.

Merkle caps optimize repeated paths by authenticating to a level below the root. Verify the path depth stops at the cap, selects the correct cap node, and that all cap nodes are transcript-bound.

## 6. Boundaries and row exceptions

Version-specific AIR domains are a frequent source of verifier/generator drift. Enumerate:

- every row;
- every row except last;
- every row except last two;
- first row;
- one-before-last row;
- last row;
- last row plus evaluation at zero;
- previous/current/next row openings;
- padding and inactive rows.

For each domain verify its vanishing polynomial, denominator, evaluation formula, and quotient degree. An incorrect domain can omit a boundary constraint or make a valid trace fail.

Check transition openings use the correct root-of-unity direction and that the verifier actually requests every shifted evaluation used by generated quotient code.

## 7. Legacy implementation checklist

- [ ] tag/commit and exact STARK verifier entrypoint are fingerprinted
- [ ] all trace/auxiliary/quotient commitment classes are mapped
- [ ] lookup and memory challenges follow all required initial commitments
- [ ] auxiliary commitments precede challenges that batch their relations
- [ ] every AIR constraint group and boundary domain reaches the quotient identity
- [ ] quotient part count/order/degree and recomposition are correct
- [ ] all evaluations at `z` and shifted points are authenticated and absorbed
- [ ] DEEP batch includes every required source polynomial once
- [ ] source-query values are linked to the FRI-tested composition polynomial
- [ ] every FRI oracle cap precedes its folding challenge
- [ ] terminal polynomial/value is fixed before query derivation
- [ ] Merkle cap, path, leaf, coset, and bit-reversal conventions match
- [ ] PoW and query counts meet the claimed concrete soundness
- [ ] historical full-statement memory/delegation/chunk aggregation is separately checked

## 8. Migration and version identification

A repository containing both GKR/WHIR and AIR/FRI modules does not necessarily
accept both proof languages. Fingerprint the invoked entrypoint, Cargo features,
generated artifact, setup format, transcript hash, and proof parser before
selecting obligations. Treat stale tests, archived generators, and retained
helpers as historical evidence until a reachable caller proves otherwise.

When helpers survived a protocol migration, re-check their semantics rather
than assuming compatibility: field/canonicalization rules, transcript padding,
Merkle leaf and cap order, query-bit extraction, extension coefficient order,
domain generators, and security-parameter tables can retain an old convention
under an unchanged function name. Compare historical tags within their own
build/configuration first, then record the exact migration delta; do not judge
one version against another version's prover format.
