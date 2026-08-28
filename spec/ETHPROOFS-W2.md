# Ethproofs W2 coverage

> External deliverable profile. These requirements organize the Airbender
> specification; they do not define Airbender's accepted relation.

## Target

W2 prepares the zkVM for an end-to-end security argument. It must identify every
proved relation, the proof invocations that establish it, their composition, their
soundness assumptions, production deviations, and the lemmas still required for W3.
The announced delivery date is 1 September 2026.

The source requirements target STARK-based RISC-V zkVMs. A substantially different
architecture requires an agreed adaptation with the EF Cryptography Team. The target
precision is sufficient for an independent reviewer to identify each component's
role, relation, assumptions, and implementation counterpart without reconstructing
the architecture from code.

For proof invocation `i`, define:

- `x_i`: public input;
- `w_i`: private witness;
- `R_i(x_i, w_i)`: proved relation;
- `pi_i`: proof;
- `epsilon_i`: claimed soundness error.

The W2 soundness claim has the form

`Verify_i(x_i, pi_i) = 1 => exists w_i: R_i(x_i, w_i)`, except with probability
at most `epsilon_i` under the stated assumptions.

## Deliverable requirements

### REQ-W2-001 — W1 foundation

Use the W1 architecture submission as the base. Retain the execution model,
segmentation, chip partition, interactions, individual-proof inventory, and recursion
overview.

The retained architecture must identify:

- program, execution trace, VM state, supported instructions, and final root claim;
- segment boundaries, carried state, chip partition, and separately proved
  precompiles or special operations;
- every bus and memory domain, the values transferred, its consistency argument,
  and the source of its challenges;
- instruction fetching, program/code binding, and the relation between fetched
  instruction, `pc`, and control flow;
- the conversion from each segment/chip to circuit or algebraic relation, including
  circuit types, boundary values, and auxiliary protocols;
- recursion topology, node relation, propagated public values, and mapping from each
  node to a concrete circuit/proof instance.

### REQ-W2-002 — Source artifact

Provide a PDF and its LaTeX, Markdown, or Typst source.

### REQ-W2-003 — Complete proof topology

Enumerate every base, recursive, aggregation, continuation, and auxiliary proof
invocation. For every edge `i -> j`, state which output of `i` becomes which input of
`j`.

The topology must include proof instances for memory, lookup, permutation,
range-check, and other auxiliary arguments.

### REQ-W2-004 — Relation per invocation

For every invocation `i`, specify:

- public input `x_i`;
- private witness `w_i`;
- relation `R_i(x_i, w_i)`;
- constraints or predicates establishing `R_i`;
- how downstream proof instances or the final verifier consume its result.

This applies to STARK/SNARK instances, auxiliary arguments, recursive-verifier
circuits, aggregation, and compression.

### REQ-W2-005 — Soundness sketch

State why acceptance implies `R_i`, subject to `epsilon_i` and explicit assumptions.
Classify every supporting lemma as standard, adapted, or new. A complete formal or
end-to-end knowledge-soundness proof is not required at W2.

### REQ-W2-006 — Baseline and production deviations

Either prove the production design directly from established component results, or:

1. define a sound vanilla construction;
2. list every soundness-relevant production deviation;
3. identify the affected layer;
4. argue that the deviation preserves soundness;
5. state interactions between deviations and any combined lemma required.

Pure performance optimizations are excluded unless they alter a relation, transcript,
constraint, commitment, low-degree test, lookup, recursion, aggregation, or another
soundness-relevant component.

### REQ-W2-007 — Auxiliary arguments are first-class

For each lookup, memory, permutation, range-check, or similar argument, specify:

- auxiliary relation;
- vanilla baseline;
- PIOP or algebraic reduction;
- committed polynomials and degree bounds;
- PCS/FRI openings;
- transcript challenges;
- soundness claim and error;
- production deviations.

Do not hide an auxiliary argument only inside an AIR/circuit description or only
inside the outer PIOP.

### REQ-W2-008 — Visible W3 obligations

List every lemma or composition argument still needed to conclude:

`Accept_final => exists valid full-program execution`.

W2 need not supply the final proof, full knowledge-soundness proof, implementation
formal verification, or documentation of non-semantic optimizations.

## Current Airbender coverage

| Requirement | Current material | Coverage |
|---|---|---|
| `REQ-W2-001` | `MACH`, `BASE`, architecture references | partial; segmentation, full interactions, and recursion need current modules |
| `REQ-W2-002` | Markdown source under `spec/` | partial; PDF packaging deferred |
| `REQ-W2-003` | module DAG in `INDEX.md` | gap; this is not yet an invocation-level topology |
| `REQ-W2-004` | `ADD` prototype; draft `MACH` and `BASE` | partial; most proof invocations have no precise relation module |
| `REQ-W2-005` | none | gap; component and composition soundness sketches required |
| `REQ-W2-006` | none | gap; vanilla baseline and deviation ledger required |
| `REQ-W2-007` | planned `GARG`, `TRANS`, `WHIR` modules | gap; auxiliary arguments need dedicated relations and reductions |
| `REQ-W2-008` | semantic `GAP-*` records | partial; proof-theoretic W3 obligations are not yet enumerated |

## Coverage gaps

- **GAP-W2-001 — Invocation topology.** Inventory the exact active base, GKR,
  auxiliary, WHIR, recursion, aggregation, and final-verifier calls and their public
  input/output edges.
- **GAP-W2-002 — Relation inventory.** Assign one relation module to every invocation
  in `GAP-W2-001`.
- **GAP-W2-003 — Vanilla/deviation ledger.** Choose the W3 proof strategy and record
  every production deviation from its baseline.
- **GAP-W2-004 — Soundness obligations.** Attach assumptions, error terms, literature
  results, adapted lemmas, and new lemmas to every relation and composition edge.
- **GAP-W2-005 — Implementation crosswalk.** Pin each segment, chip, bus, memory
  argument, proof invocation, recursion node, transcript phase, and verifier edge to
  its active implementation/configuration location and revision.

## Metadata

| ID | Authority | Source |
|---|---|---|
| `REQ-W2-001` | external deliverable | W2 `Required W2 Deliverables §0`; W1 requirements §§3.1–3.5 |
| `REQ-W2-002` | external deliverable | W2 `Required W2 Deliverables §0` |
| `REQ-W2-003` | external deliverable | W2 §1 `Recursion Topology` |
| `REQ-W2-004` | external deliverable | W2 §2 `Precise Relation for Each Proof-System Invocation` |
| `REQ-W2-005` | external deliverable | W2 §3 `Soundness Proof Sketch` |
| `REQ-W2-006` | external deliverable | W2 §3 baseline-and-deviation strategy |
| `REQ-W2-007` | external deliverable | W2 `Placement of Auxiliary Arguments` |
| `REQ-W2-008` | external deliverable | W2 `Expected Level of Detail`; `W2 does not require` |
| `GAP-W2-001` | local coverage assessment; open | module DAG is not an invocation topology at `dfb1b2a8a+dirty` |
| `GAP-W2-002` | local coverage assessment; open | current relation modules at `dfb1b2a8a+dirty` |
| `GAP-W2-003` | local coverage assessment; open | no selected vanilla construction or deviation ledger |
| `GAP-W2-004` | local coverage assessment; open | no architecture-wide soundness-obligation ledger |
| `GAP-W2-005` | local coverage assessment; open | no complete architecture-to-implementation crosswalk |

Primary source: EF Cryptography Team,
[W2 Soundness Requirements for zkVM Submissions](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf),
2 June 2026. The retained architecture checklist and applicability boundary come from
the earlier
[zkVM Architecture Whitepaper Requirements](https://crypto.ethereum.org/docs/zkvm_architecture_whitepaper_details.pdf).
The
[security-sprint announcement](https://zkevm.ethereum.foundation/blog/cryptography-research-update)
defines W2 as architecture details for buses, memory, instruction fetching, circuit
construction, and deeper recursion.
