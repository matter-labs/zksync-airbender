---
name: zk-stark-fri-verifier-review
description: Defensively audit one named legacy AIR/STARK verifier component, quotient or DEEP-ALI reduction, FRI verifier phase, generated verifier slice, or immediate STARK-to-FRI handoff. Use for deep theory-guided reviews of Rust, generated, or recursive verifier implementations and historical Airbender versions; require one fingerprinted version, verifier entrypoint, and phase rather than a repository-wide legacy audit.
---

# Focused AIR, DEEP-ALI, and FRI Verifier Review

Audit one concrete legacy STARK reduction and the protocol-specific transcript
ordering that makes it sound. Do not project current GKR assumptions onto a
historical verifier.

## Defensive correctness scope

This is an authorized, benign, read-only review of verifier correctness. Its
purpose is to identify implementation flaws so maintainers can patch them.
Limit deliverables to root cause, the precise verifier acceptance or rejection
consequence, remediation, and defensive regression tests. Use only minimal
symbolic counterexamples needed to prove a mismatch. Do not produce executable
demonstrations, operational reproduction procedures, deployment payloads,
network probes, credential/access steps, or live-system instructions.

## Require a bounded target and focus

Resolve one versioned proof-system instance and one primary focus:

- one AIR constraint-composition or quotient path;
- one boundary/transition-domain family;
- one quotient splitting/recomposition step;
- one OOD/DEEP-ALI batching seam;
- one FRI commitment, folding, query, Merkle, or terminal round;
- one small adjacent chain in a concrete generated verifier.

Fingerprint tag/commit, entrypoint, field/extension, domain, transcript/hash,
trace and quotient degree bounds, blowup, FRI schedule, security mode, generated
artifact, and caller. If the user supplies a broad verifier surface, select one
reachable verifier entrypoint, emitted artifact, and protocol phase, state that
choice, and proceed. Do not ask for narrower scope merely because several safe
choices exist. Do not review every historical tag or every constraint group in
one run.

The verifier is mandatory. Use the prover only to recover one needed oracle
order, evaluation layout, or intended deviation after reconstructing verifier
behavior. If only a prover exists, do not replace the absent acceptance predicate
with a provisional review. Keep producer-only quotient, cache, or proof-generation
defects as non-evaluable producer-parity history.

### Use theory to drive a deep implementation audit

Recover the selected phase's mathematical acceptance obligations first, but keep
that recovery compact. Theory determines which identities, degree/domain rules,
and challenge dependencies the verifier must enforce. Spend most of the run
checking how the concrete verifier implements those obligations; do not turn the
deliverable into a protocol tutorial.

The emitted verifier source selected by a reachable caller is the primary audit
artifact. Use raw circuit/layout data to recover operand meaning and use a
generator when its structure or semantic accessors make the emitted code easier
to navigate. Agreement between raw, generated, and emitted files proves only
parity; it does not prove that their shared equation implements the theoretical
invariant. Judge the equation itself.

Trace the selected phase from parsed proof values through its concrete equations
and rejection/success control flow. Credit a generator defect only after finding
the wrong emitted relation or a concrete verifier rejection path. Consult prover
or witness code only for an unresolved format or intended relation.

### Require concrete implementation evidence

Audit relations added by the verifier or verifier generator, rather than carried
verbatim from the circuit artifact, as a separate constraint class. For every
theoretical obligation in the selected slice, record the exact emitted verifier
equation or branch, its concrete operands, the proof or trusted source of those
operands, the active configuration, and how failure reaches rejection. A claim
such as “checked,” “consistent,” or “same layout” is not a closure without the
actual expressions, indices/ranges, or values that establish it.

Do not declare semantic checking of individual verifier-added or generated AIR
relations out of scope. Bound the phase or relation family instead, then finish
the concrete relations inside that boundary. Cross-check all verifier equations
that are supposed to consume the same theoretical object. They must resolve to
the same authenticated polynomial, or the verifier must enforce an equality or
copy relation between the distinct polynomials using authenticated operands.
Names, types, proximity, positional conventions, and shared helpers do not
establish identity or equality.

For every stateful argument, explicitly place every transition,
shifted-opening, first-row, and last-row reference side by side. The obligation
cannot be closed unless they resolve to the same authenticated polynomial or an
enforced equality connects them.

### Prove theory-to-implementation correspondence

Do not annotate concrete code with plausible protocol labels and call that a
check. Start from each mathematical identity in the selected phase, name every
logical polynomial, claim, domain point, and equality it requires, and enumerate
every verifier use of those objects. Resolve each use through the actual layout,
parser, accessor, generator, emitted expression, and caller to the concrete
authenticated polynomial or value it consumes. If two uses resolve to distinct
objects, locate and verify the enforced equality/copy relation between them;
otherwise the theoretical identity is not implemented. Close the obligation
only after all of its concrete uses and joins have been resolved explicitly.

### Generated implementation pass

Perform an implementation-level pass in addition to the protocol review.
Whenever verifier-generation code locates a circuit value using an index, range,
offset, collection position, or layout accessor, check the raw layout to confirm
that it selects the named value in every supported circuit configuration. Test
minimum and maximum sizes and feature combinations, and verify that neighboring
layout changes cannot silently redirect the access to another value. Confirm
that the emitted verifier consumes exactly the corresponding proof elements.

Do not confuse memory or index safety with semantic correctness. Follow every
selection helper or accessor used by the chosen relation to its implementation,
establish its preconditions, and evaluate what it returns under each active
configuration. Then trace that concrete return value into the emitted
expression and confirm that it denotes the intended protocol object. Safe
execution, an in-bounds result, or a successful build does not establish that.

Exploratory search results are navigation aids, not implementation coverage. If
a broad search is capped, truncated, or dominated by neighboring helpers, open
the exact definitions and their call sites directly. Do not close an obligation
from filenames, match counts, summaries, or generated-file parity while any
helper, branch, conversion, or selected operand on its acceptance path remains
unresolved.

Apply the same scrutiny to branching, defaults, conversions, cursor advancement,
and collection-length assumptions that affect generated expressions or proof
parsing. Rust type safety and successful code generation do not establish that
the emitted verifier implements the intended relation.

Evaluate selectors and accessors using the concrete metadata of each active
configuration. Textual equality between a generator output and an emitted copy,
or a semantically suggestive field name, is not evidence about the value selected
at runtime or generation time.

### Exhaust the bounded implementation slice

Scoping chooses a manageable acceptance slice; it does not permit sampling the
implementation inside that slice. Build a file-and-symbol coverage ledger from
the selected caller, reachable verifier control flow, generated artifact,
generator definitions, layout/parser helpers, and immediate rejection path.
Inspect every acceptance-relevant entry in that ledger or mark the obligation
unreviewed. A report is not complete merely because representative files,
relation counts, or several neighboring helpers were checked.

When the bounded slice is still too large for one context and independent
delegation is available and explicitly permitted, partition disjoint files or
implementation obligations among subagents. Give each reviewer the same
theoretical object definitions and require concrete source evidence. Reserve a
separate integration pass for cross-file identities, shared operands, parser-to-
equation mappings, and generator-to-emitted behavior; no local reviewer may
infer those joins from another reviewer's label. Without delegation, narrow the
phase further or inspect the ledger sequentially rather than silently omitting
implementation files.

## Mandatory local transcript contract

Reconstruct only the selected phase's interactive dependencies before
Fiat-Shamir. Check that trace/setup/auxiliary/quotient/FRI commitments, claimed evaluations, round
oracles, final polynomial, PoW nonce, and query openings precede the challenges
that randomize or select them. The phase specialist owns these rows even when a
separate transcript audit exists. Record broader transcript or global-composition
concerns as handoffs; do not let them displace the selected STARK/FRI
implementation review.

## Read the applicable references

Always read:

- [legacy AIR, DEEP-ALI, and FRI](../zk-verifier-review/references/stark-deep-fri.md)
- [Fiat-Shamir transcript](../zk-verifier-review/references/fiat-shamir.md)

For detailed specification recovery, read
[normative sources](../zk-verifier-review/references/normative-sources-expanded.md).
Use a current Airbender profile only as a migration contrast; fingerprint the
historical tag from its own entrypoint and source.

## Workflow

1. Fingerprint one reachable verifier entrypoint, emitted artifact, active
   configuration, caller, and selected phase.
2. State the phase's theoretical acceptance obligations concisely: the exact
   identities, domains/degrees, authenticated claims, and local challenge
   dependencies that soundness or completeness requires.
3. For each obligation, inspect the emitted verifier implementation and record
   its exact equation/branch, concrete operands and sources, configuration, and
   rejection path. Use generator or raw layout code only to clarify this emitted
   behavior.
4. Stress the implementation mechanisms that select or consume those operands:
   indexing/ranges, offset arithmetic, branching/defaults, supported layout
   variants, parser/cursor accounting, field conversions, and shifted-domain
   conventions.
5. Check the selected phase's local transcript order and immediate incoming and
   outgoing claim handoffs. Keep unrelated transcript, aggregation, and producer
   issues as separate leads.
6. Finish every obligation in the selected slice even after finding a candidate.
   Classify each as verified, a verifier soundness/completeness finding, a latent
   verifier defect, or explicitly unreviewed.

Apply the phase-specific theory from the references:

- For AIR/quotient work, cover the selected constraint and boundary domains,
  random composition, emitted operands, quotient degree/splitting, and the OOD
  identity.
- For DEEP-ALI, cover every selected source evaluation, point/shift, coefficient
  order, denominator, authentication source, and link to the FRI-tested claim.
- For FRI, cover the selected rounds' oracle representations, fold formulas,
  domains/cosets, queries, Merkle authentication, terminal representation, PoW,
  and proof exhaustion.

## Required artifacts

### Version and phase fingerprint

```text
tag/commit; entrypoint; generated artifact; field/extension; transcript;
domains/degrees; blowup/FRI schedule; selected phase; adjacent handoffs
```

### Theory-to-verifier obligation ledger

| Theory obligation | Exact emitted verifier equation/branch | Concrete operands and their proof/trusted source | Active configuration/caller | Closure, finding, or unreviewed evidence |
|---|---|---|---|---|

Do not fill this ledger with relation-family labels alone. Include the concrete
indices, ranges, counts, expressions, or configuration values needed to verify
the implementation claim.

### DEEP/FRI claim chain

| Step | Prover object | Transcript timing | Required identity | Outgoing claim/oracle | Authentication/final check |
|---|---|---|---|---|---|

### Local transcript rows and soundness terms

Record all selected-phase challenges and quantitative assumptions. Do not claim
whole-system security bits from a local phase.

## Evidence gate

Confirm a soundness finding only with the exact historical invariant, prover
freedom, all constraint/transcript/opening checks, reachable tag/configuration,
and a bounded symbolic accepting flow for a false AIR or low-degree claim. Keep
it non-executable. Separate completeness, stale-code, and specification issues.

A plausible neighboring issue is a lead until it has an exact verifier
acceptance/rejection path and a soundness or completeness consequence. Record it
briefly and continue the obligation ledger. Finding one issue never authorizes
ending the selected verifier review with obligations unchecked.

Preserve an exact defect in unreachable verifier source or an emitted verifier
artifact as a separate **latent finding** when its activation condition is
concrete. Do not give it deployed severity or claim a present acceptance path.
A generator-only branch, stale name, TODO, or suspected migration risk without
a defective verifier artifact remains implementation history or a lead.

For generator history, distinguish three separate states: a wrong generator
branch, an emitted artifact containing that relation, and a compiled verifier
selected by a caller. Only the latter two can support a verifier example; a
wrong branch that never emitted an artifact and a deterministic malformed-source
build failure are implementation history. Do not infer a runtime domain mismatch
merely because a patch replaces a hardcoded capacity with a semantic parameter;
show the wrong emitted or executed verifier behavior. Commit titles and
defensive assertions are supporting clues, not substitutes for that flow.

## Deliverable

Report the selected historical version, phase, immediate handoffs, findings,
leads, concrete obligation ledger, local transcript dependencies, error terms,
and every unreviewed obligation in the bounded slice.

Keep the work authorized, source-local, read-only, and defensive. Do not build
proof forgeries or operational malicious provers.
