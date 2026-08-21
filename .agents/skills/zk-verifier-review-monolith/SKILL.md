---
name: zk-verifier-review-monolith
description: Defensively audit an entire Rust, generated, recursive, Solidity/Yul, or L1 zero-knowledge verifier system in one integrated monolithic run across transcript, proof inputs, Sumcheck/GKR/WHIR or STARK/DEEP-FRI, aggregation, soundness, recursion, and settlement. Use when explicitly benchmarking or preferring the historical all-in-one verifier-review workflow rather than the coordinator-plus-specialists suite; use the prover only as a protocol and format cross-reference.
---

# Defensive ZK Verifier Review

Audit the language accepted by the complete verifier system, not the behavior of the honest prover. For a focused request, resolve one complete verification entrypoint and the transitive dependencies of the selected pass. For a prover-wide or whole-system request, include every proof class, circuit family, chunk aggregator, recursion/wrapper boundary, generated/deployed verifier, and equivalent native/EVM implementation that can change the accepted statement. Return a high-precision cryptographic soundness report, not a general Rust code review.

## First principle

**Treat every prover-supplied value as adversarial freedom until the verifier has constrained it.**

For every word, field element, cap, opening, polynomial coefficient, claimed evaluation, count, tag, cached value, challenge copy, public output, and branch selector read from proof data, ask:

1. What values and encodings can the prover choose?
2. What statement or earlier value must it equal or derive from?
3. Is it absorbed before the first challenge whose security requires it to be fixed?
4. Is every semantic use checked, including all copies and cached/derived forms?
5. Can a malicious prover solve a later verification equation backward by choosing this value after seeing a challenge?

Honest-prover code cannot answer these questions affirmatively. It shows one valid strategy; it does not restrict a malicious strategy.

The second-order form is: **a challenge is random to the prover only when every value it must bind was already fixed.** Enumerate prover freedoms before enumerating verifier checks.

## Safety and review boundary

Keep the work authorized, source-local, read-only, and defensive.

- Do not generate proof forgeries, executable exploit provers, deployment payloads, network probes, or live-system attack instructions.
- Establish a soundness defect with verifier-local control-flow and algebraic evidence, a bounded symbolic malicious transcript, or a finite abstract proof flow.
- Describe the missing invariant and a defensive regression property.
- Distinguish soundness, material completeness, robustness/availability, and ordinary implementation quality. Report panics or unsafe-code issues as security findings only when they affect the requested threat model.
- Unless the request says otherwise, assess computational verifier soundness.
  State zero-knowledge/privacy leakage and proof-of-knowledge or extractor
  properties as out of scope rather than filing them as verifier findings.

## Select and fingerprint the target

Resolve the requested verifier to an exact externally reachable entrypoint, version, feature set, security level, field, transcript/hash configuration, and generated artifact. If the user names no version or target and repository context cannot resolve one safely, ask for the verifier entrypoint or commit/tag.

Do not silently review only a helper. Include every layer that can change the accepted statement:

```text
proof bytes / nondeterminism source
  -> parser and canonical decoding
  -> per-circuit verifier or generated verifier
  -> Sumcheck/GKR or AIR/quotient checks
  -> PCS / WHIR / FRI opening checks
  -> full-statement aggregation
  -> recursion/wrapper/public output
  -> Solidity/Yul calldata parser and generated runtime bytecode
  -> on-chain proof-pair/recursion-chain anchor and state-transition caller
```

For generated verifiers, audit both the generator and the exact generated or compiled output. Establish how layouts, constants, setup caps, feature flags, and security parameters reach the deployed entrypoint. Treat stale generation, wrong artifact selection, or generator/output drift as first-class risks.

### Select the review breadth

Use these modes to structure a bounded request; run transcript reconstruction first whenever another mode depends on challenges:

| Mode | Primary question |
|---|---|
| Transcript / Fiat-Shamir | Does every challenge bind the complete prior statement and protocol conversation? |
| Protocol round logic | Does every Sumcheck/GKR/STARK/PCS round enforce the paper's relation and degree? |
| Proof-input validation | Is every prover word canonical, correctly shaped, and pinned to its required domain? |
| Cross-circuit/chunk composition | Do individually valid proofs imply one valid program execution and global memory? |
| Implementation relationship | Are these mirrors of one concrete proof instance, independent proof-system instances joined by a statement boundary, or recursive wrappers—and does the required equivalence/handoff hold? |
| EVM/L1 settlement | Does the deployed Solidity/Yul path verify and anchor the exact final recursive statement, and can only successful verification authorize settlement? |
| Soundness budget | Do fields, degrees, queries, batches, grinding, and runtime bounds deliver the claimed bits? |

For a full verifier-system audit, run **all modes** and do not stop after one helper or one circuit family. Treat the transcript round table and prover-freedom ledger as shared prerequisites for every later pass.

## Load references

Always read these compact core files completely before auditing:

- [verifier-threat-model.md](references/verifier-threat-model.md)
- [methodology.md](references/methodology.md)
- [fiat-shamir.md](references/fiat-shamir.md)
- [proof-data-validation.md](references/proof-data-validation.md)
- [finding-format.md](references/finding-format.md)

Then read only the applicable protocol and architecture references. These are
the canonical references for their topics; there is no compact/expanded pair
to load twice:

- Rust, generated Rust, `unsafe`, Cargo features, or nondeterminism streams: [rust-verifier-surfaces.md](references/rust-verifier-surfaces.md)
- GKR, multilinear Sumcheck, batched layer claims, or early termination: [sumcheck-and-gkr-expanded.md](references/sumcheck-and-gkr-expanded.md)
- WHIR, multilinear PCS verification, Merkle openings, or folding: [pcs-whir-expanded.md](references/pcs-whir-expanded.md)
- legacy AIR, quotient, DEEP-ALI, or FRI: [stark-deep-fri.md](references/stark-deep-fri.md)
- Airbender: [airbender-verifier-architecture.md](references/airbender-verifier-architecture.md)
- multiple circuits, chunks, delegation, memory, recursion, or aggregation: [cross-circuit-and-aggregation-expanded.md](references/cross-circuit-and-aggregation-expanded.md)
- Solidity/Yul, `verifier_evm/`, an L1 verifier, split verifier transactions, a registry, recursive-chain settlement, or deployed bytecode: [evm-l1-verifier.md](references/evm-l1-verifier.md)
- grinding or soundness parameters: [grinding-and-soundness-budget-expanded.md](references/grinding-and-soundness-budget-expanded.md)
- papers and implementation-audit background: [normative-sources-expanded.md](references/normative-sources-expanded.md)
- for the matching snapshot only, [airbender-gkr-v1-profile.md](references/airbender-gkr-v1-profile.md) after its applicability check

For a full-system audit, read each applicable reference completely when starting
its corresponding pass; do not load every protocol file before touching source.
A focused audit reads only the files needed for its selected mode. Precedence:
this `SKILL.md` defines workflow; core and protocol references define normative
review/evidence rules; versioned project profiles provide conditional search
leads only after their applicability checks. If guidance conflicts, follow that
order and record the conflict. [finding-format.md](references/finding-format.md)
alone owns the report headings and numbering.

If the companion skill is installed, load its relevant circuit-side interface references as optional enrichment:

- [global argument scope](../zk-circuit-review/references/global-arguments-scope.md)
- [GKR wiring and aggregation](../zk-circuit-review/references/gkr-wiring-and-aggregation.md)
- [lookups and LogUp](../zk-circuit-review/references/lookups-and-logup.md)
- [memory and RAM](../zk-circuit-review/references/memory-and-ram.md)
- [padding](../zk-circuit-review/references/padding.md)
- [public I/O binding](../zk-circuit-review/references/public-io-binding.md)

Do not assume a historical Airbender protocol from the current tree. Fingerprint the target first and reconstruct its version delta.

## Reconstruct the protocol from the verifier

Start from the verifier entrypoint and produce four coupled artifacts before judging findings.

### 1. Accepted-statement dossier

Record:

- public statement, program/circuit identity, setup/verifier key, public inputs and outputs;
- proof classes, circuit families, allowed chunk counts and trace sizes;
- field and extension field, domains, degree bounds, blowup/folding schedules, query counts, cap sizes, and security level;
- for every implementation, the concrete proof-system instance tuple
  `(field, extension, transcript hash, encoding, commitments, parameters)` and
  whether it is a mirror, independent outer instance, or recursive boundary;
- recursion layer and final output encoding;
- L1 settlement contract, authorized caller, deployed verifier address/code hash, compiler/EVM target, transaction split, and what on-chain state change acceptance enables;
- global memory, delegation, lookup, PC/timestamp, initialization, teardown, and padding invariants;
- project deviations from the cited protocol papers.
- provenance of trusted setup caps, verifier keys, imported/generated constants,
  program binaries, and final-PC/security constants, including reproducible
  regeneration and deployed-artifact comparison.

### 2. Proof-data ledger

Enumerate every prover-controlled item in parser order. For each item record:

| Item | Parsed at | Domain code accepts | Domain protocol requires | Absorbed before dependent challenge? | What pins it | Later uses/status |
|---|---|---|---|---|---|---|

Include lengths, counts, optional/empty sections, enum tags, duplicate copies, caches, caps, nonces, query leaves, paths, and final claimed values. A valid pin is a timely transcript binding plus sound later check, an algebraic equality, an authenticated commitment opening, a recomputation-and-used comparison, or a structural impossibility. Mark residual freedom, unchecked or debug-only assertions, ignored comparison results, and vacuous empty-container success explicitly.

For Solidity/Yul, make the ledger byte-accurate: record every calldata offset and width, out-of-range load behavior, high-bit mask or canonicality check, memory destination/lifetime, and exact final cursor. Also record every external call's target, caller authorization, success-bit handling, returndata requirements, and persistent-state effect.

### 3. Interactive-round and transcript schedule

First reconstruct the interactive protocol without Fiat-Shamir. Then map its verifier messages to transcript squeezes:

| Round | Prior verifier claim | Prover message fixed now | Absorb encoding/order | Challenge sampled | Challenge role | Required later check |
|---|---|---|---|---|---|---|

For every challenge, write its full dependency set. A later challenge must depend on the complete state that produced every earlier challenge plus every intervening prover message. Compare the verifier schedule independently with the prover schedule; agreement is necessary but not sufficient.

### 4. Claim and composition graph

Trace each verification-relevant claim from authoritative origin to final statement:

```text
statement/setup/commitment
  -> challenge-dependent relation
  -> claimed evaluation or product
  -> Sumcheck/quotient reduction
  -> PCS opening
  -> per-proof verifier output
  -> cross-proof accumulator
  -> recursive chain/public output
  -> deployed verifier result or authenticated registry state
  -> L1 state-transition authorization
```

Mutual consistency is not provenance. A group of prover-supplied values may satisfy all equations among themselves while remaining unbound to the committed witness, setup, statement, or earlier claim.

## Run the review passes

Pass 0 is mandatory: finish the verifier-derived interactive/transcript schedule,
challenge dependency sets, and proof-data ledger before any challenge-dependent
pass. This satisfies the transcript-first rule.

Use this default effort priority:

| Priority | Review domains |
|---|---|
| **P0 — highest** | Fiat-Shamir/transcript, proof-input validation, and cross-circuit/chunk/global composition |
| **P1 — middle** | The active GKR/WHIR or STARK/DEEP-ALI/FRI algebraic backend and its same-instance generated artifacts |
| **P2 — later boundary** | Recursion, verifier binaries, Solidity/Yul, deployed L1 verification, and settlement integration |
| **P3 — final quantitative pass** | Concrete field, proximity, query, batching, grinding, hash, retry, and union-bound soundness accounting |

Priority controls default order and depth, not severity. Promote P2 to P0 or P1
when the selected target is recursive, deployed, on-chain, or settlement-facing.
Audit only the active P1 backend unless the target explicitly spans current GKR
and historical STARK implementations. During fingerprinting, perform a cheap
soundness sanity scan for disabled or zero parameters, incoherent fields,
missing PoW, and obviously wrong query counts; perform the full theorem-driven
budget only at P3 when its inputs are known.

Then run the deeper passes in this order while finishing every applicable pass:

1. **Fiat-Shamir, parser, and proof-data deep pass (P0).** Using pass 0, check complete absorption, exact order, statement/context binding, domain separation, challenge independence, serialization, branching, state resets/forks, canonical field decoding, length/count arithmetic, unused data, duplicate or cached values, cap/path geometry, optional sections, batching coverage, PoW placement, and release-vs-debug behavior.
2. **Cross-circuit, cross-chunk, and global composition (P0).** Check challenge continuity, accumulator coverage, setup equality, circuit/type identity, count handling, empty cases, padding, PC/timestamp continuity, delegation closure, final memory equality, and every verifier-injected boundary term.
3. **Active protocol algebra (P1).** For GKR/WHIR use the GKR reference; for STARK/DEEP-FRI use the legacy reference. Check every round equation, degree bound, claimed evaluation, random linear combination, opening, final reduction, and protocol-specific transcript row.
4. **Generator, trusted constants, and active-instance equivalence (P1).** Compare program/circuit source, setup/key generation, imported constants, generator, generated verifier, flattening/serialization code, proof writer, and feature-selected binary. For genuine mirrors compare seed, absorb grouping, canonicalization, draw advancement, PoW mutation, branches, rejection, and proof framing. For independent outer instances verify the statement handoff rather than demanding proof portability.
5. **Recursion, verifier binary, and L1 acceptance boundaries (P2).** Check recursion-chain genesis/extension/termination, inner-program and verifier-key identity, public-output binding, generated binary selection, Solidity/Yul template and bytecode, deployed code hash/address, registry/wrapper authorization, and the exact statement the settlement caller trusts.
6. **EVM execution semantics and integration (P2).** Check exact calldata exhaustion, zero-padding reads, 256-bit-versus-field arithmetic, memory/spill aliasing, low-level-call success, registry authorization and idempotence, transaction atomicity, caller return handling, deploy-time parameter immutability, proxy/upgradability assumptions, gas/code-size reachability, and chain/fork-specific deployment behavior. A successful transaction is not proof acceptance unless the state-transition caller consumes an authenticated verifier success result.
7. **Parameters and concrete soundness accounting (P3).** Recompute field-size, algebraic, proximity, query, folding, batching, hash, retry, deployment-lifetime union-bound, and grinding assumptions from the enforced configuration. Ensure runtime sizes respect analyzed bounds and security-level features select coherent constants and binaries.

Use the prover only after the verifier-derived model exists. Read it to identify omitted messages, mismatched order/serialization, intended formulas, unsupported verifier paths, or specification gaps. Never dismiss a candidate because the honest prover does not exercise the malicious freedom.

## Analyze candidates adversarially

For each prover-controlled value, maximize its available freedom. Attempt to:

- choose it after a challenge that should bind it;
- select mutually consistent but uncommitted claims;
- exploit a missing item in a batch or accumulator;
- replay a proof across statements, circuits, versions, security levels, recursion layers, or chains;
- mark a proof-pair registry from an unauthorized sender, pair halves from different proof contexts, or invoke settlement through a path that ignores a revert/false result;
- use a noncanonical or ambiguous encoding;
- take an empty, zero-length, padding, or alternative-branch path that skips absorption or validation;
- exploit a trusted duplicate, cache, supplied challenge, cap, count, or setup value;
- isolate one chunk/circuit that unbalances a global argument while another component closes only aggregate equality;
- grind or reuse challenges more cheaply than the soundness analysis assumes.

Search exhaustively for downstream checks before confirming a gap. A later check closes a candidate only if it binds the same value, on every reachable branch, to its authoritative origin and before all dependent challenges.

Before trusting a rejection, prove the deployed caller honors it: `debug_assert!` is not a release check; an ignored `Result` or `bool` is not rejection; a check behind the wrong `cfg` is absent; a guest panic is rejection only if the outer execution contract treats it as non-acceptance; and a Solidity/Yul `call`/`staticcall` whose success bit is discarded is not an enforced cross-contract check. Confirm that no fallback, proxy, registry, relayer, or settlement branch converts failed verification into an authorized state transition.

## Evidence gate

Confirm a soundness finding only when all conditions hold:

1. State the intended invariant from a protocol source, repository contract, or unavoidable verifier claim.
2. Identify the exact prover-controlled freedom and all parsing/absorption/checking paths.
3. Enumerate every direct and indirect check that could bind it.
4. Give a bounded symbolic malicious transcript or algebraic assignment showing the verifier accepts while the intended statement or protocol relation is false. Keep it non-executable.
5. Establish reachability under features, generated artifacts, counts, padding, security level, wrapper entrypoints, compiler settings, deployed bytecode/address, EVM fork, caller authorization, and transaction ordering.
6. Trace impact through PCS and composition to the final accepted statement.
7. Survive a skeptical re-read aimed at disproving the candidate.

Place incomplete candidates under unverified leads or specification questions. Do not inflate findings.

For concrete-security findings, a security-level feature name alone is not a
claim or a reachable instance. Require an end-to-end build/test or generation
path that selects the level, constructs the proof, emits the matching verifier
or artifact, and consumes the defective parameter; record build reachability and
deployment reachability separately. A later fix or PR statement proves neither.

For grinding findings, identify the exact bad-challenge event and single-shot
probability, then state the adversarial work/attempt model. Never treat `b` PoW
bits as `b` information-theoretic soundness bits, add PoW counts from distinct
phases, or infer a system-wide level from one local retry-cost gap. If every
reachable configuration derives zero bits, the new mechanism is hardening or
future support rather than evidence of a historical security failure.

Classify active defective protocol code as **implementation-only** when neither
a consuming acceptance path nor a concrete honest-proof rejection path is
established. A hypothetical future verifier copying a prover bug is not present
soundness, and an intended transcript that no verifier implements is not by
itself present completeness.

Confirm completeness only when the affected generated binary, contract, prover,
or wrapper was actually buildable/reachable and a canonical honest artifact is
shown to reject, panic, or fail to compose. A source fragment fixed before the
first compiling verifier is latent rather than historical completeness.
Canonicalization or field-representation hardening is implementation-only unless
an exact consumer distinguishes the old representation in an accepting or
rejecting predicate.

Maintain a separate latent-findings section. Preserve an exact defect when its
violated invariant and activation condition are established but no current
caller, feature, generated artifact, binary, contract, or deployment reaches
it. Label it **latent**, withhold deployed severity and present false-acceptance
claims, and state what would activate it. Speculative TODOs or missing evidence
remain leads; reachable completeness and robustness failures are not latent.

## Independent validation

When delegation is available and permitted, separate discovery into transcript, protocol algebra/PCS, composition, and parser/generator roles. Give each proposed finding to a fresh skeptical validator with source artifacts and the invariant, but not the desired conclusion. Ask it to locate a closing check or disprove reachability. Preserve the defensive boundary.

When delegation is unavailable, run the roles sequentially and re-read the source from the entrypoint before validation. Never claim independent validation unless it occurred.

## Deliverable

Use [finding-format.md](references/finding-format.md) as the authoritative outline.
Include the four reconstruction artifacts, exact coverage limits, a candidate-disposition and
verified-closures ledger, and separate confirmed soundness, completeness,
robustness, and non-security observations.

For a full-system audit also include an implementation-relationship table,
quantitative soundness budget, and deployment/settlement trust map. When the
EVM/L1 path is in scope, state whether it verifies one base chunk, one unified
recursion chunk, or only a final recursive proof; never infer that boundary from
a contract name. When maintaining this skill, preserve
[design-requirements.md](references/design-requirements.md).
