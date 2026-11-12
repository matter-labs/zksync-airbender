# Ethproofs W3 coverage

> External deliverable profile. These requirements organize the Airbender
> specification; they do not define Airbender's accepted relation.

## Publication status

As of 16 September 2026, the EF Cryptography Team has not published a dedicated W3
requirements document. The official requirements repository contains the January
architecture-whitepaper guidelines and the June W2 requirements, but no W3 file.
The January guidelines said that precise W3 requirements would be published on
1 July 2026.

This document therefore separates:

- the W3 requirements that are already stated in official sources; and
- a local readiness checklist derived from W2, which is not an official W3
  checklist and may need reconciliation when precise requirements appear.

## Authoritative sources

- EF Cryptography Team,
  [Towards a zkVM architecture whitepaper](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/1f69cec5e343a5ae2cf2021609c2fed5e3c50a99/resources/zkvm_architecture_whitepaper_details.pdf),
  29 January 2026. Section 5 supplies the currently published W3 target.
- EF Cryptography Team,
  [W2 Soundness Requirements for zkVM Submissions](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf),
  2 June 2026. This identifies the component claims, assumptions, and proof
  obligations that W2 must expose for the full W3 proof.
- EF Cryptography Team,
  [zkEVM Security Sprint: February Update](https://zkevm.ethereum.foundation/blog/cryptography-research-update),
  11 February 2026. This fixes the W3 deadline at 1 December 2026 and describes W3
  as the security-argument milestone.
- EF Cryptography Team,
  [official requirements repository](https://github.com/khovratovich/zkvm-ef-security-sprint/tree/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources).
  At the inspected revision it contains no dedicated W3 requirements file.

## Target

W3 is the final announced architecture-whitepaper phase. It must give a security
argument showing that the zkVM implements a sound argument of knowledge. In the
terminology of the official overview, the argument must explain why final-proof
acceptance implies the existence of an execution of the original program that
respects the VM semantics.

For final public input `x`, final proof `pi`, and the full-program execution
relation `R_VM`, the target consequence is:

`Verify_final(x, pi) = 1 => exists w_exec: R_VM(x, w_exec)`,

except with the claimed total error under the stated assumptions. Because the source
calls for an *argument of knowledge*, the final W3 document must also state the
knowledge or extraction notion that justifies this existence claim. The public source
does not yet define that notion or its exact formalism.

## Published deliverable requirements

These are the requirements currently stated by official sources. They intentionally
do not add the missing precision that the promised W3 document was expected to
supply.

### REQ-W3-001 — W1 and W2 foundation

Build the final security argument over the execution architecture, proof-invocation
topology, per-invocation relations, assumptions, baseline/deviation strategy, and
remaining lemma inventory prepared in W1 and W2.

### REQ-W3-002 — Sound argument of knowledge

Provide a proof sketch demonstrating that the zkVM implements a sound argument of
knowledge. State the security notion, quantified adversary, extractor or equivalent
knowledge guarantee, probability space, assumptions, and claimed error precisely
enough for an independent cryptographic review.

### REQ-W3-003 — Valid original-program execution

Show why acceptance of the final proof implies the existence of a full execution of
the original program that respects the selected VM semantics. The argument must bind
the extracted execution to the final public claim and cannot stop at the validity of
an isolated circuit, segment, auxiliary argument, or recursive layer.

## Derived readiness checklist

The following checklist is a local derivation from the W2 obligations. It is the
minimum work currently visible for reaching `REQ-W3-002..003`; it is not represented
as an official EF checklist.

1. **Close the invocation graph.** Enumerate every base, GKR/Sumcheck, WHIR/PCS,
   lookup, memory, permutation, range-check, recursive, aggregation, continuation,
   and final-verifier invocation, with exact multiplicities and field-level edges.
2. **Prove each invocation claim.** For every invocation `i`, establish the stated
   knowledge-soundness theorem for `R_i(x_i, w_i)`, including public-input binding,
   assumptions, extractor interface, and concrete error.
3. **Discharge auxiliary arguments.** Prove the algebraic reductions and openings
   for lookup, memory, permutation, range-check, and other global arguments instead
   of treating them as unnamed parts of the outer circuit proof.
4. **Justify the production protocol.** Complete either the direct proof of the
   production system or the vanilla construction plus every soundness-preserving
   deviation and interaction lemma selected in W2.
5. **Prove recursive composition and extraction.** Show that every producer output
   is bound to the named consumer input and that recursive or aggregated knowledge
   extraction composes along every accepting path.
6. **Recover one VM execution.** Compose the segment, chip, instruction, memory,
   lookup, boundary, and continuity relations into one witness satisfying the
   full-program execution relation.
7. **Bind the terminal claim.** Connect program identity, initial state, final state,
   application output, proof parameters, recursive chain, and the selected terminal
   verifier or L1 acceptance condition.
8. **Compute the total error.** Account for invocation multiplicity, batching,
   challenge reuse, adaptive ordering, Fiat–Shamir, grinding, algebraic errors,
   cryptographic binding, and recursive composition without omission or
   double-counting.

## Completion test

An external reviewer should be able to answer all of the following from the W3
deliverable:

- What exact full-program relation and public claim does the final verifier accept?
- What knowledge-soundness or extraction notion is claimed, against which adversary,
  and under which assumptions?
- Why does every accepted proof-system invocation yield the witness or relation output
  consumed by the next invocation?
- Why are every lookup, memory, permutation, range-check, and other auxiliary claim
  sound?
- Why do segmentation, chip partitioning, padding, and recursion neither omit nor
  duplicate any part of the execution?
- Why does the composed witness describe one execution of the supplied original
  program under the selected VM semantics?
- Which production deviations from the proof baselines are covered by standard,
  adapted, or new lemmas?
- What is the concrete final error bound, and how is each term counted?
- Which exact production profile, code revision, proof artifact, and terminal verifier
  does the theorem cover?

## Current Airbender coverage

| Requirement | Current material | Coverage |
|---|---|---|
| `REQ-W3-001` | [W2 crosswalk](ETHPROOFS-W2.md), component modules, [proof profiles](profiles/), [topology](recursion/topology.md), and [soundness ledger](soundness/accounting.md) | partial; the W2 crosswalk still reports incomplete topology, relation, baseline/deviation, soundness, and implementation mapping |
| `REQ-W3-002` | per-invocation theorem schema and lemma categories in `REQ-SOUND-001..004`; global-product candidate bound in [GP-SND](soundness/memory.md) | partial; no adopted extractor model, complete component proofs, concrete invocation-wide error bounds, or end-to-end knowledge-soundness theorem |
| `REQ-W3-003` | ISA relations, shared [execution](execution/), [memory](memory/), [lookup](lookups/), [base acceptance](recursion/base.md), and provisional recursive [topology](recursion/topology.md) | partial; no proof yet composes these relations into one valid full-program execution bound to the selected terminal acceptance path |

### Readiness coverage

| Derived item | Current material | Missing for W3 readiness |
|---|---|---|
| Invocation graph | `TOPO` | production path, exact cardinalities, field interfaces, auxiliary edges, and terminal artifact |
| Per-invocation claims | `SOUND`, `BASE`, and component relations | complete knowledge-soundness proofs, extractor interfaces, assumptions, and concrete errors |
| Auxiliary arguments | `LOOKUP`, `MEM`, and `GP-SND` | complete PIOP/PCS reductions, challenge schedule, degree bounds, zero-factor policy, and error terms |
| Production justification | `SOUND` schema | adopted vanilla baselines or a direct-production proof, complete deviation ledger, and interaction lemmas |
| Recursive composition | `TOPO` and `BASE` | extraction/composition theorem for all recursion, bridge, continuation, and final-verifier edges |
| Full VM execution | ISA, execution, memory, and lookup modules | adopted cross-module theorem for segmentation, continuity, global closure, and exact VM semantics |
| Terminal claim | `BASE` and experimental `REQ-TOPO-005` | selected production terminal path, public-input policy, deployed identities, and external acceptance consumer |
| Total error | `SOUND` | exact production parameters, invocation multiplicities, mechanism bounds, and `epsilon_final` |

## Coverage gaps

- **GAP-W3-001 — Precise external checklist.** Reconcile this document when the EF
  Cryptography Team publishes or otherwise confirms the detailed W3 requirements,
  knowledge notion, expected rigor, format, and review criteria.
- **GAP-W3-002 — Knowledge-soundness model.** Select and state the adversary,
  extractor access, auxiliary-input model, Fiat–Shamir model, recursive-extraction
  model, assumptions, and success/error definition used by Airbender.
- **GAP-W3-003 — Component proof ledger.** Complete the standard, adapted, and new
  lemmas for every proof invocation, auxiliary argument, production deviation, and
  producer/consumer edge.
- **GAP-W3-004 — Full-execution composition.** Prove that the extracted component
  witnesses form exactly one execution of the supplied program, including segment
  coverage, state continuity, instruction semantics, memory closure, and terminal
  state.
- **GAP-W3-005 — Production theorem boundary.** Select the production profiles,
  parameter sets, recursion route, hash modes, final verifier, public claim, code
  revision, and artifact format covered by the theorem.
- **GAP-W3-006 — Concrete total error.** Discharge `GAP-SOUND-001..005` and compute
  the final bound for every selected production target.

## Later milestones

The published architecture-whitepaper program has exactly three phases: W1, W2, and
W3. The January guidelines call W3 the final phase, and the February update lists no
W4. No official W4 deliverable or requirements document was identified as of
16 September 2026. Later zkVM security, formal-verification, audit, and deployment
work may continue under other roadmaps, but it should not be labeled W4 without a new
EF source.

## Metadata

- external requirements revision: `khovratovich/zkvm-ef-security-sprint@a7726ff41058bb96f8c8d12975339f4bfe75878c`
- coverage implementation: `zksync-airbender@31dcc31b8aa2+dirty`
- external profile: `W3 architecture-whitepaper security argument`

| ID | Authority | Source |
|---|---|---|
| `REQ-W3-001` | external deliverable | [architecture guidelines §§2.3 and 5](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/1f69cec5e343a5ae2cf2021609c2fed5e3c50a99/resources/zkvm_architecture_whitepaper_details.pdf); [W2 purpose and remaining W3 obligations](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) |
| `REQ-W3-002` | external deliverable | [architecture guidelines §5](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/1f69cec5e343a5ae2cf2021609c2fed5e3c50a99/resources/zkvm_architecture_whitepaper_details.pdf) |
| `REQ-W3-003` | external deliverable | [architecture guidelines §5](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/1f69cec5e343a5ae2cf2021609c2fed5e3c50a99/resources/zkvm_architecture_whitepaper_details.pdf) |
| `GAP-W3-001` | local publication assessment; open | [official resources at `a7726ff41058bb96f8c8d12975339f4bfe75878c`](https://github.com/khovratovich/zkvm-ef-security-sprint/tree/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources) contain only the architecture guidelines and W2 requirements |
| `GAP-W3-002` | local coverage assessment; open | no adopted Airbender knowledge-soundness or extraction model at `31dcc31b8aa2+dirty` |
| `GAP-W3-003` | local coverage assessment; open | `GAP-SOUND-003..004` and incomplete component proof obligations at `31dcc31b8aa2+dirty` |
| `GAP-W3-004` | local coverage assessment; open | `REQ-SOUND-006` remains an obligation rather than an established theorem |
| `GAP-W3-005` | local coverage assessment; open | `GAP-TOPO-001,005`, `GAP-BASE-003..004`, and incomplete profile manifests |
| `GAP-W3-006` | local coverage assessment; open | `GAP-SOUND-001..005` |
