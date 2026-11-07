# Shared review helpers

These modules define the common language and context of the review claims: value
representations, public decoding, native rows and ports, initialized state, and
logical matching. They state how a witness is interpreted and which public
conditions a claim uses. Whole-run execution conclusions belong in Trace.

## Claims and supporting connections

Supporting [memory proofs](Memory/README.md#logical-memory-result) derive chronological
history and latest-write reads from initialized matching and clock constraints.
[Decoder connections](Decoder/README.md#checked-connections) establish original
public decoding and preserve it through state updates.
[Context results](Context/README.md#checked-connections) recover native order and
boundary ranges. [Delegation](Delegation/README.md#checked-connections) and
[unified context](UnifiedReduced/README.md#checked-results) extend the same
history interpretation to workers and joint windows.

These results justify the inputs used by circuit and execution claims. They do
not turn the explicit logical permutations into cryptographic proofs or establish
every remaining caller/padding obligation.

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
