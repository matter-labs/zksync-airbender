# Fiat-Shamir Transcript Audit

## Contents

1. Security model
2. Mandatory reconstruction
3. Absorption completeness
4. Ordering rules
5. Serialization and challenge mapping
6. State-machine failures
7. Batching and composition
8. Audit checklist

## 1. Security model

Fiat-Shamir replaces each public-coin verifier message with a random-oracle challenge derived from the statement and the interactive transcript **up to that point**. The implementation must preserve both causality and context.

The required shape is:

```text
seed_0 = H(domain || protocol/version || complete public statement/context)
seed_i = H(seed_{i-1} || canonical_encode(prover_message_i))
challenge_i = ExpandAndMap(seed_i, round/challenge domain)
```

Equivalent sponge constructions are valid if they preserve the same properties. Airbender may hash a current seed followed by new data rather than use labeled sponge calls; audit the concrete construction, not the notation.

In a hash-chained transcript, an absorb is a new hash invocation rather than a
write into persistent sponge state. The implementation frames the prior seed
and new message into one canonical byte string and computes a new digest. The
hash function internally divides that byte string into compression blocks and
applies its specified padding, length, and final-block rules; those internal
boundaries must not change which bytes the protocol absorbs. In particular,
hashing one concatenated message and chaining several hash calls are different
transcript operations unless the protocol explicitly defines the latter. A
sponge instead retains permutation state across absorb and squeeze operations,
so its rate, padding, and operation boundaries define the corresponding byte
stream. Reconstruct whichever model the implementation actually uses.

The essential rule is stronger than “prover and verifier match”: every value whose later choice could help satisfy a challenge-dependent verification equation must be fixed in the transcript before that challenge is sampled. Two implementations can match each other and still implement an unsound schedule.

## 2. Mandatory reconstruction

### Recover the interactive protocol first

For each round write:

```text
P -> V: message M_i
V checks any immediate relation on M_i
V -> P: fresh independent challenge c_i
```

Then replace the verifier message with a squeeze. This answers the key ordering question for Sumcheck: the prover sends the current round polynomial; the verifier checks its degree and `g_i(0)+g_i(1)=current_claim`; only then is the fresh folding point `r_i` sampled and the claim updated to `g_i(r_i)`.

### Build the concrete schedule

Do not summarize a compound proof as one row. Include:

- initial statement/context absorption;
- every commitment or cap;
- lookup/permutation challenges;
- claimed output/evaluation batches;
- each Sumcheck round polynomial and round challenge;
- final-step evaluations and next-layer batching challenge;
- PCS batching challenge;
- each WHIR/FRI oracle commitment, out-of-domain sample, fold challenge, PoW nonce, and query derivation;
- final polynomial/monomial data;
- recursion and outer aggregation transcripts.

Use this table:

| # | Transcript state before | Prover-controlled data read | Exact absorbed words/bytes | Immediate validation | Challenge/PoW | Later dependent objects |
|---|---|---|---|---|---|---|

Compare verifier, prover, proof flattener/serializer, and any recursive in-circuit verifier. Record conditional paths independently.

## 3. Absorption completeness

### Bind the statement and context

Unless an explicit higher-level binding proves equivalence, include or authenticate:

- all public inputs and claimed public outputs;
- circuit/program identity, shape, layout, and constraint/system version;
- verifier/setup key or a binding commitment to it;
- field, domain, extension, degree/blowup/folding parameters when not compiled constants;
- security level, transcript hash variant, reduced-round mode, and protocol mode;
- recursion layer, inner proof kind, aggregation arity, and chain/application domain when relevant;
- any fixed/preprocessed table commitments;
- externally injected initial/final machine state.

Hashing a digest of context is valid only if the digest is collision-resistant for a canonical, complete encoding and the verifier authenticates the expected digest.

### Bind every prover message before dependent randomness

Commonly omitted items include:

- trace/witness/memory/setup/quotient/auxiliary oracle commitments;
- multiplicity columns and permutation/LogUp auxiliaries;
- claimed circuit outputs and boundary values;
- out-of-domain evaluations;
- final-step and cached/virtual polynomial evaluations;
- Merkle caps rather than only a subset/root surrogate;
- final low-degree polynomial coefficients or exposed terminal leaves;
- per-proof counts, types, or ordering choices that select the verified relation;
- inner proof public inputs, verifier key, and recursion metadata.

Absorb the complete structure. Check loops for off-by-one omissions, capacity-versus-length confusion, partial slices, only-first-cap errors, and fields skipped because they are duplicated elsewhere.

### Bind before, not merely eventually

Late absorption does not repair causality. Examples:

- memory/lookup witness commitments must precede memory/lookup challenges;
- a Sumcheck polynomial must precede its round challenge;
- all items in a random linear combination must precede the batching challenge;
- a FRI/WHIR folded-oracle commitment must precede the next folding randomness;
- all queried oracle commitments and terminal data must precede query-index derivation;
- claimed evaluations must be fixed before a challenge used to batch or relate them.

## 4. Ordering rules

For challenge `c`, calculate two sets:

```text
AvailableBefore(c) = all statement and prover data fixed in transcript before c
RequiredBefore(c)  = all values assumed fixed in the soundness argument for c
```

Require `RequiredBefore(c) subseteq AvailableBefore(c)` in the same canonical order on every branch.

Then calculate:

```text
UsedAfter(c) = all verification equations and protocol roles using c
```

If one challenge is used for several roles, justify that the paper's analysis permits this correlation. Otherwise require distinct squeezes or domain-separated derivations.

For multi-round protocols, `c_i` must inherit the full prefix that produced `c_1,...,c_{i-1}` plus every intervening prover message. A verifier that reconstructs `c_i` from only `c_{i-1}` is safe only if `c_{i-1}` is itself an unambiguous binding digest with sufficient entropy and the derivation preserves domain separation.

## 5. Serialization and challenge mapping

### Canonical encodings

Check:

- unique representation for base and extension field elements;
- rejection or well-defined reduction of out-of-range integers;
- coefficient/limb order and endianness;
- fixed-width versus variable-width encodings;
- unambiguous list boundaries, lengths, optional variants, and enum tags;
- structural padding and zero padding;
- Merkle cap node order and complete cap length;
- architecture-independent layout; do not hash Rust padding, pointers, `usize`, or unstable enum layout;
- same meaningful data length on prover, native verifier, and recursive verifier.

If fixed widths and a fixed schedule are relied on instead of explicit length prefixes or labels, verify every width and branch is fixed by authenticated context. Concatenation must be injective over reachable transcript objects.

### Mapping hash output to challenges

Check:

- byte/word expansion and counter progression;
- field reduction bias and whether the proof assumes uniform challenges;
- extension-field coefficient construction;
- truncation, skipped words, and digest-block rounding;
- forbidden or exceptional challenges such as zero or denominator roots;
- repeated draws from the same seed and whether the seed evolves;
- different routines used immediately after PoW;
- query-bit extraction, ignored prefix words, bit order, and modulo/bias behavior.

Prover and verifier agreement is again necessary but not enough: calculate whether the resulting challenge distribution meets the soundness proof.

## 6. State-machine failures

Audit all transcript state transitions for:

- reset to an initial/default seed in the middle of a proof;
- clone/fork where later branches fail to rejoin or intentionally share challenges without proof;
- finalization that discards buffered data;
- absorbing after a draw into a stale seed;
- helper routines that bypass the transcript and read a prover-supplied “challenge”;
- supplied challenges recomputed but never compared;
- conditional or empty-message paths that skip an update;
- distinct transcript APIs with different padding/finalization semantics;
- challenge calls that do not mutate state, causing reuse;
- PoW verification that mutates the seed differently from prover grinding;
- recursion code reconstructing a different schedule from the native verifier.

For each draw API, write the relation between pre-draw seed, returned challenge
blocks, and post-draw seed. Some designs leave the seed unchanged for a
single-block draw or make it equal to the last returned digest for a multi-block
draw. That behavior is not automatically a bug, but it invalidates any reasoning
that treats transcript state as hidden or domain-separated from challenge
material and can make consecutive draws identical.

Inspect buffered hash implementations carefully: the current seed, pending buffer, active word count, zero padding, and reset/finalize action all affect the transcript. Assertions about block alignment are cryptographic invariants, not mere performance hints.

## 7. Batching and composition

For each batching challenge, create an ordered manifest:

| Batch | Items | Coefficients | Commitment/provenance | Absorbed before challenge? | Collision degree/error |
|---|---|---|---|---|---|

Check that:

- every batched item is included exactly once;
- prover and verifier share order, signs, and exponent convention;
- challenges are not reused across independent batches without analysis;
- batch identity, size, and item type are bound;
- empty and singleton batches have defined behavior;
- nested batching accounts for correlated challenges and total degree;
- cross-proof aggregation cannot reorder, omit, duplicate, or substitute items;
- shared external challenges are demonstrably identical across every proof class and field of the challenge tuple.

## 8. Cross-implementation relationship

Classify the relationship before comparing transcripts:

1. **Mirrors of one proof instance** must agree byte-for-byte on statement
   encoding, absorption grouping, padding, draw advancement, challenge mapping,
   PoW, branches, and accepted proof language.
2. **Independent proof instances joined by a statement boundary** may use
   different fields, hashes, encodings, and transcripts. Do not demand proof
   portability; prove that the outer statement authenticates every required
   output and identity of the inner instance.
3. **Recursive wrappers** must bind the inner verifier program/key, public
   inputs and outputs, recursion level or base/step mode, and prior chain value.

For same-instance mirrors, compare the initial seed, absorb granularity,
encoding, draw word consumption and state advancement, grinding, conditional
paths, and terminal cursor. A parity document is a claim to verify against both
implementations, not evidence by itself.

## 9. Audit checklist

### Missing transcript elements

- [ ] public inputs/outputs
- [ ] circuit/program/domain/version identity
- [ ] verifier/setup key and fixed-table commitments
- [ ] every oracle commitment or Merkle cap
- [ ] claimed outputs/evaluations and cached values
- [ ] proof counts/types/order metadata
- [ ] recursion context and inner statement

### Wrong order

- [ ] witness/auxiliary commitments before lookup/permutation challenges
- [ ] Sumcheck polynomial before its round challenge
- [ ] full evaluation batch before batching challenge
- [ ] folded oracle cap before next fold challenge
- [ ] terminal data and all caps before query indices
- [ ] complete prior transcript before every later challenge

### Reuse and separation

- [ ] independent challenge roles use independent/domain-separated draws
- [ ] proof classes, circuits, versions, layers, and sessions cannot replay
- [ ] transcript forks/resets are intentional and justified

### Encoding and parsing

- [ ] canonical field encodings
- [ ] injective concatenation and explicit/fixed lengths
- [ ] prover/native/recursive serialization equality
- [ ] optional/empty branches consume and absorb consistently
- [ ] challenge reduction and bit extraction match security analysis

### Semantic validation

- [ ] every prover value is checked against its authoritative origin
- [ ] duplicate/cached/supplied derived values are recomputed or compared
- [ ] absorption is not mistaken for validation
- [ ] a malicious prover cannot choose a free value after seeing its dependent challenge

The practical test is always the same: freeze the transcript at each squeeze and list every variable the prover can still choose. If any such variable participates in the security argument for that challenge, investigate until a prior binding or a sound alternative argument is established.

Maintain a verified-closures table alongside candidates. For recurring false
positives such as alleged concatenation ambiguity, record the exact mechanism
that closes them—fixed authenticated widths, final-block active-length binding,
explicit length tags, or a canonical enclosing digest—and the feature/version
where it applies. Revalidate closures after transcript refactors rather than
re-deriving or blindly trusting them.
