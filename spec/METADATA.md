# Specification metadata

Metadata records how to interpret and compose canonical claims. Implementation
mapping belongs in audit output, not in the specification.

## Record model

| Field | Encoding | Rule |
|---|---|---|
| `id` | inline `KIND-MODULE-NNN` label | one canonical definition |
| `claim` | text beside the ID | the complete normative statement or open question |
| `authority` | ID kind and cited basis | never inferred from implementation alone |
| `activation` | condition in the claim | required when the claim is conditional |
| `depends` | `## Imports` plus cited IDs | only semantic dependencies, not navigation |
| `discharged-by` | cited `OUT-*` or external boundary | required for an `ASM-*` consumed by another module |
| `source` | public standard, paper, or project decision | no repository path, symbol, or line anchor |
| `exported` | boundary stated in an `OUT-*` claim | distinguish module, system, and public output |
| `affects` | IDs, ID family, or bounded scope in a `GAP-*` | state what the gap prevents establishing |

Do not duplicate the claim in a metadata table. Put each field in the canonical claim,
its enclosing section, or the module's `soundness.md` when it applies to the whole
module.

Prototype cleanup may renumber IDs. Once an ID is cited by an external audit or other
artifact, preserve it or explicitly migrate the reference.

## Authority

| Prefix | Meaning |
|---|---|
| `TGT-*` | supported proving or verification target |
| `IN-*` | relation input |
| `ASM-*` | imported or external premise |
| `REQ-*` | normative end-state relation or acceptance condition |
| `OUT-*` | claim exported across a stated boundary |
| `DEV-*` | confirmed mismatch in the assessed implementation |
| `GAP-*` | unresolved decision, fact, or proof obligation |

An authored `REQ-*` is an explicit project choice of intended behavior. Papers define
protocol baselines and support security claims. External standards define intended ISA
behavior where adopted. Implementation evidence can confirm a relation or a deviation,
but cannot by itself weaken a `REQ-*`.

Do not encode intended behavior as provisional. If the end state is known, state a
`REQ-*` and record current drift as a `DEV-*`. If the end state is not known, record a
`GAP-*` and its affected scope.

## Activation and dependencies

A conditional claim states its activation in the claim itself, for example
`on execute = 1` or `when the channel is present`. Unconditional claims need no
repeated `activation: always` annotation.

A file with normative cross-file dependencies declares exactly one block of this form,
using paths relative to `spec/`:

```text
## Imports

- `protocols/sumcheck/verifier.md`
```

Only entries in this block are imports. Ordinary Markdown links are navigation.
Statement-level dependencies cite exact IDs, a validated numeric range, or a validated
ID family. The import graph must be acyclic.

## Assumptions, outputs, and gaps

An `ASM-*` consumed by another module identifies either the `OUT-*` that discharges it
or an explicit external boundary such as the cryptographic model or admitted program.

An `OUT-*` states whether it crosses only a module boundary, the proof-system boundary,
or the public verification boundary.

A `GAP-*` asks one unresolved question and names the IDs, ID family, or narrowly bounded
scope it affects. Cite available evidence. A decision owner may be named when useful,
but task assignment is workflow state and is not normative.

## Audit mapping

The specification does not name source files, symbols, or line numbers. An audit maps
canonical IDs to code in the assessed implementation revision and records that mapping
in its output. Code movement alone must not require a specification change.

Paper and standard citations use public links. Local reference copies may be used while
checking the specification but are not part of the published specification.

Executable conformance checks, content hashes, binding status, and regression-coverage
tags belong in audit tooling or audit output. `spec/check.py` validates only the
specification's own structure and references.

## File shape

A mechanism directory contains only the files needed to separate these roles:

- `INDEX.md` — navigation only;
- `relation.md` — the accepted mathematical relation, including its terminal equality,
  nonzero, range, and rejection conditions;
- `protocol.md` — messages, challenges, round structure, and claim flow;
- `verifier.md` — transcript-driven, stream-driven, or cross-proof acceptance procedure
  when that procedure is substantial enough to separate from the relation;
- `soundness.md` — baseline, adaptations, assumptions, and open proof obligations.

Do not create `verifier.md` merely to repeat a relation's terminal checks. When a
separate verifier exists, it imports the relation or protocol it verifies and states
only the additional verification procedure.
