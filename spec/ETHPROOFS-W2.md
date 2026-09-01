# Ethproofs W2 coverage

> External deliverable profile. These requirements organize the Airbender
> specification; they do not define Airbender's accepted relation.

## Authoritative sources

- EF Cryptography Team,
  [W2 Soundness Requirements for zkVM Submissions](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf),
  2 June 2026. This is the controlling W2 checklist.
- EF Cryptography Team,
  [Towards a zkVM architecture whitepaper](https://crypto.ethereum.org/docs/zkvm_architecture_whitepaper_details.pdf),
  29 January 2026. W2 requires the W1 architecture submission described in
  sections 3.1--3.5 as its basis.
- Ethereum Foundation,
  [Cryptography Research Update](https://zkevm.ethereum.foundation/blog/cryptography-research-update).
  This announcement supplies program context; it is not a substitute for the two
  requirements documents above.

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
- execution-trace segmentation, segment boundaries, carried state, chip partition,
  and separately proved precompiles or special operations;
- every memory organization and bus, the values transferred, its consistency
  argument, and the source of its challenges;
- instruction fetching, program/code binding, and the relation between fetched
  instruction, `pc`, and control flow;
- the conversion from each segment/chip to circuit or algebraic relation, including
  boundary values, circuit types, the number and parameters of each circuit type,
  commitment schemes, argument types, and auxiliary protocols;
- recursion topology, each node's NP relation, propagated public values, and mapping
  from every node to a concrete circuit/proof instance.

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
The sketch may be an informal proof, a chain of lemmas, standard references plus new
obligations, or a combination of these. Classify every supporting lemma as standard,
adapted, or new. A complete formal or end-to-end knowledge-soundness proof is not
required at W2.

### REQ-W2-006 — Baseline and production deviations

Either describe the production design directly, treating third-party components as
black boxes under explicit established results and assumptions, or use the following
baseline-and-deviation strategy:

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

## Completion test

An external reviewer must be able to answer all of the following from the W2
deliverable:

- What exact relation does each proof-system invocation prove? `REQ-W2-003..004`.
- What is the clean vanilla proof system for each relation? `REQ-W2-006..007`.
- How does the production protocol differ from that vanilla construction?
  `REQ-W2-006..007`.
- Which differences change the proof system rather than only its implementation?
  `REQ-W2-006`.
- What soundness theorem is expected for the vanilla construction? `REQ-W2-005..007`.
- Which lemmas are standard, adapted from literature, or new? `REQ-W2-005`.
- Which proof and composition obligations remain for W3? `REQ-W2-008`.

## Current Airbender coverage

| Requirement | Current material | Coverage |
|---|---|---|
| `REQ-W2-001` | `UPROF`, `UNIFIED`, `PRECOMP`, shared machine modules, `MACH`, `BASE`, and `TOPO` | partial; exact segmentation/cardinality and complete recursion interfaces remain open |
| `REQ-W2-002` | Markdown source under `spec/` | partial; PDF packaging deferred |
| `REQ-W2-003` | invocation hierarchy and known producer/consumer edges in `TOPO` | partial; exact counts, field-level interfaces, auxiliary edges, and the selected terminal path remain open |
| `REQ-W2-004` | `ADD`, `BSHIFT`, `JUMP`, `MULDIV`, `MWORD`, `MEMSUB`, shared machine modules, `LOOKUP`, and `BASE` | partial; unified embedded relations, precompile computations, and several proof-layer invocation relations remain incomplete |
| `REQ-W2-005` | theorem schema and obligation inventory in `SOUND` | partial; component sketches, concrete errors, and supporting lemmas remain gaps |
| `REQ-W2-006` | baseline/deviation requirements and empty production ledger in `SOUND` | partial; no adopted vanilla baselines or complete deviation ledger yet |
| `REQ-W2-007` | machine-side lookup/range relation in `LOOKUP` and placement in `TOPO` | partial; transcript order, PIOP reduction, committed polynomials, openings, and error terms remain gaps |
| `REQ-W2-008` | explicit W3-obligation structure in `SOUND` plus module `GAP-*` records | partial; the final obligation set depends on completing topology, relations, and error accounting |

## Coverage gaps

- **GAP-W2-001 — Invocation topology.** Complete `TOPO` with the exact active base,
  GKR, auxiliary, WHIR, recursion, aggregation, and final-verifier calls and every
  field-level public input/output edge.
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
| `REQ-W2-001` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) `Required W2 Deliverables §0`; [W1](https://crypto.ethereum.org/docs/zkvm_architecture_whitepaper_details.pdf) §§3.1–3.5 |
| `REQ-W2-002` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) `Required W2 Deliverables §0` |
| `REQ-W2-003` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) §1 `Recursion Topology` |
| `REQ-W2-004` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) §2 `Precise Relation for Each Proof-System Invocation` |
| `REQ-W2-005` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) §3 `Soundness Proof Sketch` |
| `REQ-W2-006` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) §3 baseline-and-deviation strategy |
| `REQ-W2-007` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) `Placement of Auxiliary Arguments` |
| `REQ-W2-008` | external deliverable | [W2](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) `Expected Level of Detail`; `W2 does not require` |
| `GAP-W2-001` | local coverage assessment; open | `TOPO` identifies the hierarchy and several stream edges, but its invocation-count, field-interface, auxiliary-edge, and terminal-path gaps remain open |
| `GAP-W2-002` | local coverage assessment; open | current relation modules at `dfb1b2a8a+dirty` |
| `GAP-W2-003` | local coverage assessment; open | no selected vanilla construction or deviation ledger |
| `GAP-W2-004` | local coverage assessment; open | no architecture-wide soundness-obligation ledger |
| `GAP-W2-005` | local coverage assessment; open | no complete architecture-to-implementation crosswalk |
