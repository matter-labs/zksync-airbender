# SOUND: Soundness accounting

> W2/W3 ledger for proof-system error terms, assumptions, lemmas, deviations, and composition; this module does not yet assert an end-to-end soundness theorem.

`*` marks a provisional assumption whose exact invocation, component, or transcript
input remains incomplete under the gaps below.

## Guarantee

A completed instance of this ledger assigns a soundness statement to every proof
invocation and composition edge, accounts for every error source, and exposes the
remaining W3 obligations. At the inspected revision, the ledger is a schema with open
entries; no concrete total error bound follows from this document.

## Requirement basis

This module implements the accounting requested by the EF Cryptography Team's
[W2 Soundness Requirements for zkVM Submissions](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf),
especially the soundness-sketch, production-deviation, auxiliary-argument, and visible
W3-obligation requirements. [ETHPROOFS-W2.md](../ETHPROOFS-W2.md) is the local
requirements crosswalk.

## Symbols

- `I` — finite set of proof-system invocations.
- `E` — directed invocation edges; `i -> j` identifies the output of `i` consumed by
  `j`.
- `x_i`, `w_i`, `R_i`, `Verify_i` — public input, private witness, relation, and
  verifier for invocation `i`.
- `A_i` — explicit algebraic and cryptographic assumptions used by invocation `i`.
- `epsilon_i in [0, 1]` — claimed soundness error for invocation `i`; this is a
  placeholder until a concrete bound is supplied.
- `epsilon_final in [0, 1]` — total claimed error after all invocations and
  composition edges are accounted for.

## Assumptions

- **`ASM-SOUND-001`\* — Invocation graph.** `I`, `E`, invocation multiplicities, and
  exact consumed-output mappings are imported from `external:TOPO`.
- **`ASM-SOUND-002`\* — Component relations.** Each `(x_i, w_i, R_i, Verify_i)` is
  imported directly from its owner in `external:BASE`, `external:GKR`,
  `external:WHIR`, `external:LOOKUP`, `external:MEM`, `external:RECUR`, or
  `external:PUB`.
- **`ASM-SOUND-003`\* — Transcript schedule.** The ordered absorbed messages, sampled
  challenges, domains, retries, and proof-exhaustion rule are imported from
  `external:TRANS`.

These assumptions define the accounting boundary. They do not assert that the named
external modules are complete.

## Requirements

### REQ-SOUND-001 — Per-invocation claim

For every `i in I`, the ledger states a concrete theorem of the form

`Verify_i(x_i, pi_i) = 1 => exists w_i: R_i(x_i, w_i)`,

except with probability at most `epsilon_i` under `A_i`. It identifies the quantified
adversary, probability space, public-input binding, and knowledge-versus-ordinary
soundness notion.

### REQ-SOUND-002 — Mechanism error budget

For every `i`, `epsilon_i` is a concrete bound decomposed into every mechanism used by
that invocation: transcript/Fiat-Shamir reduction, GKR or Sumcheck, WHIR/PCS proximity
and opening, lookup/memory/permutation reduction, recursion or aggregation, and
cryptographic binding. A mechanism absent from `i` contributes no term; an unquantified
term leaves the entry incomplete.

### REQ-SOUND-003 — Lemma register

Every step supporting `REQ-SOUND-001` or `REQ-SOUND-002` is classified as:

- **standard** — applied under cited hypotheses without protocol changes;
- **adapted** — derived from a cited result with the adaptation and new proof
  obligation stated; or
- **new** — requires a project-specific lemma and proof.

The ledger maps each lemma to the invocation, edge, assumptions, and error terms it
discharges.

### REQ-SOUND-004 — Vanilla and production deviations

For every proof mechanism, the ledger names a vanilla construction and enumerates each
soundness-relevant production deviation. Each deviation records its affected relation
or layer, changed assumptions or error terms, interactions with other deviations, and
the lemma that justifies the production construction.

### REQ-SOUND-005 — Composition bound

For every `i -> j in E`, the ledger states the lemma that binds the named output of `i`
to the named input of `j`. The resulting `epsilon_final` accounts for invocation
multiplicity, batching, challenge reuse or independence, adaptive ordering, recursive
composition, and all cryptographic assumptions without double-counting or omitting an
acceptance path.

### REQ-SOUND-006 — W3 end-to-end obligation

The ledger identifies every premise still needed to derive

`Accept_final => exists a valid full-program execution`,

except with probability at most `epsilon_final`. Unproved premises remain explicit W3
obligations and are not treated as established conclusions.

## Open boundary

- **GAP-SOUND-001 — Complete invocation multiplicities.** `external:TOPO` does not yet
  enumerate every base, auxiliary, GKR, WHIR, recursive, aggregation, and final-verifier
  invocation or every exact edge, so the index set for a total bound is unknown.
- **GAP-SOUND-002 — Concrete production budget.** Select the production proof targets
  and record, per invocation, the exact field and extension, degree bounds, query and
  repetition counts, LDE and fold schedules, PoW, cap sizes, hash modes, and resulting
  error terms. Configuration labels such as `Sec100` are not themselves a derivation.
- **GAP-SOUND-003 — Lemma classification.** Supply citations and hypotheses for
  standard results, proofs of every adaptation, and statements of every new lemma for
  transcript, GKR/Sumcheck, WHIR/PCS, lookup/memory/permutation, and recursive
  composition.
- **GAP-SOUND-004 — Production deviation ledger.** Choose each vanilla baseline and
  exhaustively classify implementation choices that can affect soundness, including
  configured conjecture modes, reduced-round hashing, custom global arguments,
  batching, and recursion-specific schedules.
- **GAP-SOUND-005 — Final composition theorem.** Prove the edge-binding and
  composition lemmas that turn the component claims into `REQ-SOUND-006`, then compute
  `epsilon_final` for each selected production target.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: `production candidates; normative target selection open`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-SOUND-001` | provisional | always | `external:TOPO` | located | `repo:prover_pipeline/src/lib.rs#ProofTarget@dfb1b2a8a` | `symbol:prover_pipeline/src/lib.rs#ProofTarget`; `symbol:prover_pipeline/src/lib.rs#ProofCounts` |
| `ASM-SOUND-002` | provisional | always | `external:BASE`; `external:GKR`; `external:WHIR`; `external:LOOKUP`; `external:MEM`; `external:RECUR`; `external:PUB` | prose | incomplete relation modules at `dfb1b2a8a` | — |
| `ASM-SOUND-003` | provisional | always | `external:TRANS` | located | `repo:transcript/src/lib.rs#Transcript@dfb1b2a8a`; `repo:verifier_common/src/gkr/mod.rs#make_initial_transcript@dfb1b2a8a` | `symbol:transcript/src/lib.rs#Transcript`; `symbol:verifier_common/src/gkr/mod.rs#make_initial_transcript` |
| `REQ-SOUND-001` | normative | every `i in I` | `ASM-SOUND-001..003` | prose | [W2 §3](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `REQ-SOUND-002` | normative | every `i in I` | `REQ-SOUND-001`; `ASM-SOUND-003` | prose | [W2 §§2–3 and auxiliary arguments](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `REQ-SOUND-003` | normative | every supporting lemma | `REQ-SOUND-001..002` | prose | [W2 §3](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `REQ-SOUND-004` | normative | every proof mechanism | `REQ-SOUND-001..003` | prose | [W2 §3 baseline and deviations](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `REQ-SOUND-005` | normative | every `i -> j in E` and final composition | `ASM-SOUND-001..003`; `REQ-SOUND-001..004` | prose | [W2 §§1–3](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `REQ-SOUND-006` | normative | selected final verifier | `REQ-SOUND-001..005` | prose | [W2 visible W3 obligations](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/a7726ff41058bb96f8c8d12975339f4bfe75878c/resources/w2-requirements.pdf) | — |
| `GAP-SOUND-001` | open | — | affects `ASM-SOUND-001`, `REQ-SOUND-001`, `REQ-SOUND-005`; owner: human | — | incomplete `external:TOPO` at `dfb1b2a8a` | — |
| `GAP-SOUND-002` | open | — | affects `REQ-SOUND-002`, `REQ-SOUND-005..006`; owner: human | — | `repo:prover/src/definitions/mod.rs#SecurityLevel@dfb1b2a8a`; `repo:prover/src/gkr/prover_config/example_configs.rs#config_for_security_level_under_pessimistic_conjecture@dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#SecurityLevel`; `symbol:prover/src/gkr/prover_config/example_configs.rs#config_for_security_level_under_pessimistic_conjecture` |
| `GAP-SOUND-003` | open | — | affects `ASM-SOUND-002`, `REQ-SOUND-001..003`, `REQ-SOUND-005..006`; owner: human | — | no accepted lemma register at `dfb1b2a8a` | — |
| `GAP-SOUND-004` | open | — | affects `ASM-SOUND-003`, `REQ-SOUND-004..006`; owner: human | — | `repo:prover/src/gkr/prover_config/example_configs.rs#config_for_100_bits_under_pessimistic_conjecture@dfb1b2a8a`; `repo:prover/src/definitions/mod.rs#USE_REDUCED_BLAKE2_ROUNDS@dfb1b2a8a`; custom lookup/global-product implementation | `symbol:prover/src/gkr/prover_config/example_configs.rs#config_for_100_bits_under_pessimistic_conjecture`; `symbol:prover/src/definitions/mod.rs#USE_REDUCED_BLAKE2_ROUNDS`; `symbol:cs/src/definitions/gkr/lookup.rs#SingleColumnLookupRelation`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#GrandProductAccumulationStep` |
| `GAP-SOUND-005` | open | — | affects `REQ-SOUND-005..006`; owner: human | — | no end-to-end composition proof at `dfb1b2a8a` | — |
