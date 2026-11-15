# Verifier-First Review Methodology

## Contents

1. Objective and threat model
2. Scope resolution
3. Specification recovery
4. Control-flow reconstruction
5. Data and claim ledgers
6. Adversarial review passes
7. Candidate validation
8. Completion criteria

## 1. Objective and threat model

The object under review is the predicate implemented by the verifier:

```text
Accept(statement, proof, verifier_configuration) -> bool
```

A sound verifier should accept only proofs for statements in the intended language, up to the explicitly budgeted cryptographic soundness error. The malicious prover controls the entire proof byte/word stream, all proof-level ordering choices permitted by the parser, and usually the choice of statement unless an external caller fixes it.

Classify verifier inputs as:

- externally trusted statement/context;
- fixed verifier configuration or compiled constants;
- setup/verifier key that is either trusted, authenticated, or itself part of the statement;
- prover-controlled proof data;
- challenges recomputed by the verifier;
- values derived and checked by the verifier;
- values returned by an inner verifier and consumed by an aggregator.

Do not treat a typed Rust value as validated. A `Field` value can be noncanonical before conversion, an enum can be decoded from an arbitrary tag, an array can contain unverified values, and a value returned by a helper can still be prover-supplied under another name.

## 2. Scope resolution

Resolve the following before detailed analysis:

| Dimension | Questions |
|---|---|
| Entry | Which public function/binary/circuit invokes verification? |
| Version | Commit/tag/branch; current or historical protocol generation? |
| Build | Features, target architecture, security level, field, hash rounds, generated files? |
| Statement | What public inputs, program/circuit/setup identities, and outputs are accepted? |
| Proof classes | Base, recursion, unified, unrolled, delegation/precompile, setup-free? |
| Protocol | GKR+WHIR, AIR+DEEP-ALI+FRI, or another composition? |
| Serialization | Bytes, `u32` words, nondeterminism source, field limbs, endianness? |
| Deployment | Which generated verifier and wrapper are actually selected? |
| L1/EVM | Which Solidity/Yul source, compiler/settings, runtime bytecode/address, registry/helper/proxy, transaction sequence, and settlement caller define acceptance? |

Then write one exact sentence describing what an accepting run proves, including
the statement inputs, setup/program identity, parameters, and where the claim
ends: one chunk, one aggregate, a recursion chain, or an authorized L1 state
transition. Revisit that sentence whenever a discovered caller or wrapper moves
the boundary.

Trace call sites repository-wide before marking a path unused. For historical tags, inspect named files by exact tag and record the delta from the nearest documented profile.

## 3. Specification recovery

Use sources in this order:

1. Versioned project architecture and explicit verifier contracts.
2. Protocol papers for the exact construction or its closest ancestor.
3. Verifier entrypoint and generated verifier as evidence of implementation.
4. Prover, flattener, and tests as evidence of intended message order and honest behavior.
5. Comments and names as hypotheses only.

Write down project-specific deviations. Examples include early stopping that exposes 8 or 16 evaluations, batched multi-output GKR layers, LSB-first versus MSB-first folding, Merkle caps instead of roots, reduced hash rounds, shared external memory challenges, and recursion-specific setup treatment. A paper proves only the construction it states; every deviation needs its own argument or reduction.

## 4. Control-flow reconstruction

Follow the verifier in actual parse order, including loops, branches, optional sections, feature gates, const-generic specializations, and error paths. For each read operation, record:

```text
offset -> type -> conversion -> storage -> transcript action -> algebraic action -> output
```

Check that proof flattening and parsing are true inverses for every supported shape. Compare:

- field-extension coefficient order;
- raw versus reduced field representation;
- low/high word order for `u64` values;
- Merkle cap node and oracle order;
- LSB/MSB variable and bit-reversal conventions;
- per-layer address ordering and deduplication;
- final-round special encodings;
- number and position of deliberately skipped challenge words;
- empty-oracle and zero-column behavior.

Treat trailing unread proof data, under-read proof data, and branch-dependent consumption as potential ambiguity or composition issues. Determine whether an outer parser frames proofs unambiguously.

For EVM/Yul, make this map byte-accurate and extend it through persistent
contract state: custom calldata parsing, memory placement, external-call
success/returndata, authenticated registry writers, finalization, and the
state-transition consumer. Use `evm-l1-verifier.md`.

## 5. Data and claim ledgers

### Proof-data ledger

Assign every item one disposition:

- `bound-and-checked`;
- `bound-only` (absorbed but not semantically checked);
- `checked-only` (used in an equation but not fixed before dependent randomness);
- `derived` (not prover-controlled);
- `trusted-context`;
- `unused`;
- `unresolved`.

Absorption is not semantic validation. Semantic validation is not timely commitment. Most Fiat-Shamir bugs are `checked-only`; many cache/provenance bugs are `bound-only` or neither.

### Challenge dependency ledger

For challenge `c_i`, record:

```text
c_i = MapToChallenge(H(domain || statement || transcript_before_i))
```

Expand `transcript_before_i` into concrete ordered items rather than writing “previous transcript.” Record the first verifier equation that uses `c_i`, all roles in which it is reused, and its independence assumptions.

### Claim provenance ledger

For every claim, label its authoritative origin:

- direct statement/public input;
- committed polynomial/oracle;
- earlier sumcheck/quotient claim;
- setup/fixed polynomial;
- locally recomputed expression;
- inner verifier output;
- global accumulator.

Trace an unbroken binding path. Equations among claims of unknown origin do not establish provenance.

### Candidate disposition ledger

Maintain one row per material lead:

| ID | Candidate | Prover freedom | Required invariant | Checks searched | Reachability | Disposition | Evidence gap |
|---|---|---|---|---|---|---|---|

Never silently discard a lead. Close it with the exact binding check, demote it with the missing evidence, or confirm it through the evidence gate.

Maintain a companion verified-closures ledger for recurring false positives:

| Candidate pattern | Exact closing mechanism | Source/config | Revalidated at | Reopens if |
|---|---|---|---|---|

A known closure saves audit budget only after it is rechecked against the target
version and feature path.

Maintain an assumption ledger as well: assumed primitive/property, why it is
reasonable, which verifier obligations depend on it, and what was not audited.
"Sumcheck is sound" does not excuse checking whether this implementation
actually realizes the sumcheck covered by that theorem.

## 6. Adversarial review passes

### A. Statement and context binding

- public inputs and outputs;
- circuit/program identity and shape;
- verifier/setup key or setup-cap commitment;
- protocol/version/security-level/hash configuration;
- chain/session/application domain when replay matters;
- recursion layer and inner proof type;
- chunk counts, trace sizes, and ordering metadata.

### B. Transcript and challenge ordering

Use the complete process in `fiat-shamir.md`. Reconstruct it from the verifier independently before comparing the prover.

### C. Algebra and batching

For every random linear combination, enumerate the complete ordered item set, coefficient convention (`1, alpha, ...`, independent challenges, powers, nested batches), degree, and failure probability. Check missing first/last terms, duplicate exponents, reordered arrays, zero challenges, and reuse across distinct identities.

### D. PCS and Merkle authentication

Trace each opened value to the correct commitment, oracle, column, leaf position, domain point, and cap. Verify cap geometry, depth, query-index derivation, bit order, leaf encoding, path direction, and multi-oracle batching. A valid Merkle path authenticates bytes, not their meaning.

### E. Composition

Use `cross-circuit-and-aggregation-expanded.md`. Enumerate all proof classes and every field of shared challenge/accumulator tuples. Check empty contributors and neutral elements explicitly.

### F. Parameters and soundness

Use `grinding-and-soundness-budget-expanded.md`. Recompute effective security for actual runtime bounds and all unioned checks. Do not infer soundness solely from a feature name such as `security_100`.

### G. Generator and build

Trace constants from circuit artifact/configuration into generated source and final binary. Compare regenerated output when safe. Check stale committed artifacts, feature skew, generator branches, unsupported layouts, and debug assertions that disappear in release.

Trace the reverse direction too: every trusted setup cap/key, imported generated
module, fixed program/circuit digest, delegation parameter, final PC, and security
constant must have a reproducible provenance from the intended source artifact.
Checking a prover value against the wrong trusted constant proves the wrong
statement consistently.

### H. EVM/L1 deployment and settlement

Trace generated Solidity/Yul through exact compiler settings and runtime
bytecode to the deployed address and final state-transition caller. Check
calldata exhaustion/canonicity, EVM-versus-field arithmetic, Yul memory/spill
regions, low-level-call success, registry authorization and replay/overwrite,
single-chunk memory assumptions, recursive-chain terminus, public outputs,
proxy/upgrades, gas/code size, and rejection semantics.

## 7. Candidate validation

For a possible omission, apply the closing-check search:

1. Search all uses of the value and every alias/copy.
2. Trace wrappers and consumers of returned verifier outputs.
3. Trace commitment/opening provenance.
4. Check all feature/const-generic instantiations.
5. Check whether another algebraic identity uniquely determines the value.
6. Verify that the determining identity itself is timely bound and rooted in authoritative data.

Construct the smallest non-executable witness to the flaw:

```text
Given fixed statement S and transcript prefix T,
the prover retains variables x_1,...,x_k after challenge c.
Verification imposes equations E_1,...,E_m.
Choose/solve the free variables so all E_j hold,
while invariant I(S, proof) is false.
```

It is insufficient to say “the prover can choose this.” Show why remaining checks do not remove that freedom. Conversely, do not require a full concrete forgery if the algebraic freedom and acceptance path are completely established.

## 8. Completion criteria

The review is complete only when:

- every reachable proof item has a ledger disposition;
- every challenge has a full ordered dependency set;
- every final claim has provenance to statement/setup/commitment;
- all proof classes and aggregation loops have coverage, including empty and padding paths;
- actual parameters have a soundness-accounting disposition;
- generated/deployed artifact selection is resolved;
- every material candidate is confirmed, closed, or explicitly unresolved;
- recurring known closures were revalidated for the target version rather than
  assumed from a profile.

Stop when these artifacts answer the audit question. Do not continue collecting irrelevant repository detail.
