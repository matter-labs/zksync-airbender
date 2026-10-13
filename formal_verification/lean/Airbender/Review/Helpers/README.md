# Shared review helpers

These modules define the common language and context of the review claims: value
representations, public decoding, native rows and ports, initialized state, and
logical matching. They state how a witness is interpreted and which public
conditions a claim uses. Whole-run execution conclusions belong in Trace.

[Properties](Properties.lean) is the entry point: soundness, completeness,
the circuit model and its observable relation. It imports only Clean.

| Topic | Read it for |
| --- | --- |
| [Core](Core/README.md) | Field/word representation, Sail interface and stream primitives. |
| [Decoder](Decoder/README.md) | Native metadata, public programs, fetch and clause selection. |
| [Memory](Memory/README.md) | Ports, public images, ROM interpretation and logical history. |
| [Context](Context/README.md) | Accepted rows, family registries, public boundaries and selected pre-states. |
| [Tables](Tables/README.md) | Shared modeled range, byte, subword and lookup rows. |
| [Delegation](Delegation/README.md) | Caller/worker requests, matching and worker context. |
| [Unified machine](UnifiedReduced/README.md) | Unified registry, fetch, mixed histories and window inputs. |

These are review topics, not independent assumption sets. A circuit model names
the helpers it needs; follow those imports and fields rather than assuming every
helper is required. In particular, properties do not require decoder or memory review.

The helper layer contains shared definitions and public conditions, not whole-run
realization claims. It has no transitive dependency on Review/Trace.
Bounds, reads and schedules described as derived are proved in Proofs.
[Trace](../Trace/README.md) owns execution and terminal realization.
