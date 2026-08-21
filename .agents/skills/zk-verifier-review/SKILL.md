---
name: zk-verifier-review
description: Coordinate, scope, prioritize, and integrate a multi-run defensive audit of a zero-knowledge verifier system across transcript/input, cross-circuit composition, GKR/WHIR, legacy STARK/FRI, concrete soundness, and recursion/L1 specialists. Use for prover-wide or whole-verifier campaigns, coverage planning, selecting the right specialist when scope is unclear, reconciling specialist artifacts, or reviewing an end-to-end Airbender verifier architecture; route a clearly bounded domain task to its specialist instead of attempting the whole codebase in one run.
---

# ZK Verifier Audit Coordinator

Coordinate a campaign; do not pretend one context can deeply audit every
protocol and implementation layer. The default unit of work is one cell in a
coverage matrix:

```text
one concrete entrypoint/component
  × one proof-system instance/configuration
  × one protocol phase, global invariant, or statement boundary
```

Prefer the verifier because every proof message and subargument converges at its
acceptance predicate. Use prover code as a format/specification cross-reference.
When a prover is explicitly reviewed before a verifier exists or is ready,
produce a provisional verification contract and schedule a verifier-side rerun.

## First principles

- Treat every prover-supplied value as adversarial freedom until constrained.
- A challenge is random to the prover only after every value it must protect is
  fixed in the transcript.
- Mutual consistency among prover claims is not provenance to a statement,
  commitment, setup, previous claim, or public output.
- Individually sound proof components compose only when every handoff and global
  invariant is authenticated.
- A syntactically present check may still constrain nothing. Validate its active
  coefficients, selected branch, compared result, emitted code, and reachable
  configuration rather than crediting the existence of a function or assertion.
- Confirm findings only with a reachable false accepted statement or material
  completeness failure and all possible closing checks accounted for.

Keep every review authorized, source-local, read-only, and defensive. Do not
generate forged proofs, malicious prover tooling, deployment payloads, network
probes, or live-system attack instructions.

## Require a campaign target

For planning or integration, fingerprint:

- repository and commit/tag;
- externally reachable verifier and settlement entrypoints;
- proof-system instances `(field, extension, transcript/hash, encoding, PCS,
  parameters)` and their relationships;
- generated artifacts, features, security levels, verifier keys/setup/program
  identities, and deployed binaries/contracts;
- proof classes, circuit families, chunks, aggregators, recursion layers, and
  final public/state-transition consumers.

If the user asks for a focused audit but supplies no component, phase, or
invariant, identify likely targets and ask them to choose. Do not turn ambiguity
into a repository-wide review. If the user asks for a complete audit, build the
campaign matrix and execute bounded runs; do not assign all cells to one agent
context.

## Build one shared verifier model first

For a campaign, the coordinator owns a mandatory model-building pass before
specialization. Do not let six specialists independently rediscover six
incompatible versions of the protocol. Fingerprint and hand off:

- the accepted statement and every externally trusted policy input;
- a round table from prover message through absorption, challenge, check, and
  outgoing claim;
- a prover-freedom ledger with the semantic pin for every proof-derived value;
- a claim/handoff graph across layers, proofs, recursion, and final consumers;
- an implementation-layer map covering handwritten verifier, generator,
  emitted artifact, proof producer/serializer, recursive mirror, CLI, and L1;
- the exact configurations, security levels, feature branches, and target
  artifacts that select different paths.

This is a coordinator role, not another large audit skill. A standalone
specialist reconstructs the smallest sound slice of the same model and records
its incoming and outgoing boundaries.

## Route to specialists

| Specialist | Select one bounded target | Owns | Must also check locally |
|---|---|---|---|
| `$zk-verifier-transcript-review` | One verifier/prover entrypoint or transcript phase | Complete selected transcript, parser, proof freedoms, encoding | Interactive protocol order for the selected phase |
| `$zk-verifier-composition-review` | One global invariant and all necessary participants | RAM/memory, PC/timestamp, delegation, LogUp aggregation, padding, chunk/setup coverage | Commitment timing and shared-challenge continuity |
| `$zk-gkr-whir-verifier-review` | One Sumcheck/GKR/WHIR phase, generated component, or immediate seam | Layer/claim reduction, PCS handoff, folds/openings | Every protocol-specific transcript round and local error term |
| `$zk-stark-fri-verifier-review` | One AIR/quotient/DEEP/FRI phase or historical generated component | Constraint/quotient and low-degree claim chain | Every protocol-specific transcript round and local error term |
| `$zk-verifier-soundness-review` | One exact parameterized configuration | Field/support, algebraic/proximity/query/hash/retry errors, PoW and total bits | Hypotheses and transcript placement underlying every credited term |
| `$zk-recursion-l1-verifier-review` | One binary, recursive handoff, contract flow, or settlement boundary | Artifact identity, chain/public output, calldata/state/deployment acceptance | Boundary proof inputs and transcript/statement binding |

Use `$zk-circuit-review` separately for the enforced relation of one named
circuit or tightly related small group. A verifier specialist may inspect circuit
interfaces, but it must not silently claim a full circuit-constraint audit.

Treat composition as the horizontal join of a campaign, not merely another
directory-local pass. Its target remains one invariant, but that invariant must
span every producer, verifier output, accumulator, injected boundary term, and
final consumer required to establish it. Feed it the local artifacts from all
participating protocol cells and use its discrepancies to reopen those cells.

## Overlap is a protocol interface

Do not enforce a false separation between “transcript” and “theory.” A Sumcheck
reviewer must know which polynomial precedes `r_i`; a WHIR reviewer must know
which oracle precedes its fold/query challenges; a memory reviewer must know
which commitments precede compression challenges; a recursion reviewer must
know what bound the inner public output.

Therefore:

- the transcript specialist owns the complete selected schedule and encoding;
- every protocol specialist independently owns its local transcript rows;
- composition owns shared/external challenge derivation and equality across
  participants;
- soundness owns the quantitative consequence of challenge support, dependence,
  and retry freedom;
- recursion/L1 owns re-binding at statement and implementation boundaries.

Reconcile duplicated rows. A disagreement is a lead, not editorial noise.

## Build the coverage matrix

Rows are concrete convergence points, not directories in the abstract. Typical
Airbender rows include:

- one generated per-circuit verifier reached through `verifier_common/`;
- one GKR layer/output implementation emitted by `verifier_generator/`;
- the WHIR verifier for one parameter/security schedule;
- one full-statement global invariant in `full_statement_verifier/`;
- one recursion-chain transition or verifier guest binary;
- one generated EVM GKR or WHIR contract;
- one registry/split-transaction handoff;
- one final settlement caller and deployed runtime artifact;
- one historical STARK verifier at an exact tag.

Columns are the applicable specialists or narrower focus inside them. Mark each
cell `planned`, `in progress`, `covered`, `partial`, `blocked`, or `not
applicable`, with an artifact path and dependencies. Do not infer coverage of a
row from a similar circuit family, security mode, generated artifact, field/hash
instance, or implementation language.

Overlay an implementation-layer checklist on every applicable cell. Reading a
generator does not cover its emitted verifier; reading a verifier does not cover
the proof parser or caller; reading a prover is format evidence, not acceptance
evidence. Record which layers were actually inspected.

## Prepare a run packet

Give every specialist the smallest sufficient packet:

```text
target symbol/path and entrypoint
commit/tag and configuration/features/security mode
proof-system instance tuple
selected phase/invariant/boundary
incoming statement/claim/transcript state
expected outgoing handoff
known authoritative sources and project deviations
prior artifacts to verify, not blindly trust
explicit exclusions
```

Do not preload conclusions or suspected bugs when using an independent reviewer.
Provide raw source and prior artifacts only when they are legitimate inputs.

## Default priority and campaign order

Allocate attention in this dependency order unless the requested acceptance
boundary requires promotion:

| Priority | Specialists | Default purpose |
|---|---|---|
| **P0 — highest** | Transcript/proof input and cross-circuit/global composition | Establish causal challenge binding and whether valid local proofs imply one valid global statement. Start here at verifier convergence points. |
| **P1 — middle** | GKR/WHIR or STARK/DEEP-ALI/FRI | Audit the active algebraic backend and its local transcript rows after the shared statement and challenge model exists. |
| **P2 — later boundary** | Recursion, verifier binaries, and L1/EVM acceptance | Check that the established claim survives recursive, generated, deployed, and settlement boundaries. |
| **P3 — final quantitative pass** | Concrete soundness/security accounting | Compute the complete error budget from the exact degrees, distributions, query schedules, retry freedom, and deployment lifetime established by earlier passes. |

Priority governs default audit order and effort allocation, not finding severity.
A recursion or L1 bug can be catastrophic. Promote recursion/L1 to P0 or P1
when the named target is a recursive guest, deployed verifier, Solidity/Yul
contract, or settlement path. Select only the active P1 backend: use GKR/WHIR
for current GKR systems and STARK/FRI for legacy or explicitly selected STARK
instances rather than auditing both by habit.

Perform a cheap soundness sanity scan during fingerprinting for disabled or zero
security parameters, incoherent fields, missing PoW, or obviously wrong query
counts. Reserve theorem-driven probability accounting and union bounds for P3,
after local reviewers supply the enforced parameters and hypotheses.

Execute a full campaign as follows:

1. Build the shared verifier model: statement, round table, freedom ledger,
   claim graph, artifact layers, and configuration matrix.
2. Run P0 transcript/input reviews at verifier convergence points and one P0
   composition run per highest-risk global invariant, especially memory,
   PC/timestamp, delegation, padding/chunk coverage, and deferred challenges.
3. Run the active P1 GKR/WHIR or STARK/FRI specialists per concrete
   phase/component; use their local transcript rows to challenge the complete
   transcript artifact.
4. Run P2 recursion/L1 reviews per applicable statement, binary, deployment, and
   settlement boundary, subject to the promotion rule above.
5. Run the P3 concrete soundness budget with actual degrees, counts, gaps,
   queries, challenge distributions, and deployment-scale union bounds.
6. Validate each material candidate skeptically, reconcile overlaps, and produce
   an integrated coverage and trust report.

When delegation is available and explicitly permitted, isolate runs so bulk
source context and candidate conclusions do not leak between discovery roles.
Otherwise run the same cells sequentially with separate artifacts. Never claim
independent validation unless it occurred.

## Shared handoff artifacts

Require specialists to emit compatible artifacts:

- **target fingerprint** — entrypoint, version, config, field/hash/encoding;
- **accepted-statement or boundary contract**;
- **proof-data and transcript rows** relevant to the target;
- **claim provenance/handoff table**;
- **participant or implementation relationship table** when applicable;
- **local quantitative error terms and hypotheses**;
- **candidate disposition and verified-closures ledger**;
- **coverage/exclusions and next dependent cells**.

Store audit artifacts in the repository-prescribed audit directory. Do not
commit them when repository instructions designate that directory as local.

## Integrate without laundering uncertainty

For every final claim:

1. Trace it to source evidence and the specialist artifact that established it.
2. Confirm target fingerprint/configuration compatibility across artifacts.
3. Distinguish same-instance parity from independent statement handoff.
4. Reconcile transcript rows, claim names/order, field representations, and
   parameter counts at seams.
5. Keep unresolved dependencies unresolved; one specialist's assumption is not
   another specialist's proof.
6. Deduplicate findings only after proving they share the same root freedom and
   acceptance path.
7. State which matrix cells remain partial or unreviewed.

Keep a separate latent-findings register. An exact defect whose violated
invariant and activation condition are established must not disappear merely
because no current caller, feature, generated artifact, binary, contract, or
deployment reaches it. Label it **latent**, state what would activate it, and
withhold deployed severity and present false-acceptance claims. Do not use the
label for speculative TODOs, missing evidence, or reachable completeness and
robustness failures.

Use [finding-format.md](references/finding-format.md) for the integrated report.
Read [verifier-threat-model.md](references/verifier-threat-model.md) and
[methodology.md](references/methodology.md) when planning or integrating a
campaign. For Airbender use
[airbender-verifier-architecture.md](references/airbender-verifier-architecture.md)
and apply [airbender-gkr-v1-profile.md](references/airbender-gkr-v1-profile.md)
only after its fingerprint check. Specialists route to the remaining theory and
implementation references directly.

When maintaining this suite, preserve
[design-requirements.md](references/design-requirements.md).
