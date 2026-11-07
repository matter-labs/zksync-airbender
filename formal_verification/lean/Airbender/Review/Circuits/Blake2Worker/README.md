# Native Blake2 worker review guide

[Fresh native artifact](NativeArtifact.lean), [Native source](../../../../../../cs/src/delegation/blake2_round_with_extended_control/mod.rs), [Local control root](ControlTheorems.lean), [Proof calculations](../../../Proofs/Blake2Worker/NativeControl.lean), [Import fidelity](../../../Import/Blake2Worker.lean), [Reproduction gate](../../../../scripts/check_native_blake2.py), [Theorem regressions](../../../../Tests/NativeBlake2Worker.lean), [Intake controls](../../../../Tests/NativeBlake2WorkerImport.lean).

The selected runtime worker has CSR1991 and trace2^20. Fresh352-equation,
871-variable native compilation and all296 local lookups are retained separately
from historical generated files. Its parsed layout matches the pinned historical
JSON exactly; no historical Lean worker acceptance is reused by an assumption.

The ABI exposes processor multiplicity0,ABIhigh1 and time740/741; register10
reads a state pointer with24 read/write indirects, register11 reads a message
pointer with16 readonly indirects, register12 retains its old control read and
write. All43 access descriptors and old timestamps remain. This observes
coordinates, not initialized memory values, permission/alignment or issued work.

Review owns observables and the short control theorem. Proofs derive all13 actual
Boolean flags, both high-half13bit bounds and x12 low clearing using the native
packing equations. Import consumes every local equation and scalar/timestamp/
fixed lookup; full same-read raw protocol/clock metadata stays explicit and
uninterpreted. The local control root remains generic in the explicit four-field setup; the separately certified native fixed pool is now available below. Existing main-circuit intake remains fail closed.

Positive control slices cover only16 actual equations, including zero and
multiple round flags. They do not establish complete native acceptance, valid
round scheduling, v3F02/F03/F04 reproduction or a defect. ABI alignment/addresses/ranges, processing flags/clocks, full memory matching,
reference state/round effects, issued/unissued request/auxiliary/accumulator
connections, fulfillment/converse/accounting/terminal/protocol remain open.
General compiler/Rust/JSON/physical/field/LDE/crypto/completeness boundaries and
main CSR/MOP execution are unchanged. No native production code is modified.

## Actual native fixed pool

[Native literal pool](../../../../artifacts/setup/blake2-fixed-native.json), [Table model](Tables.lean), [Membership/output roots](TablesTheorems.lean), [XOR7 certificate](../../../Proofs/Blake2Worker/Xor7Certificate.lean), [XOR9 certificate](../../../Proofs/Blake2Worker/Xor9Certificate.lean), [Literal importer](../../../Import/Blake2Fixed.lean), [Native reproduction](../../../../scripts/check_blake2_fixed.py), [Regressions](../../../../Tests/NativeBlake2Fixed.lean), [Intake controls](../../../../Tests/NativeBlake2FixedImport.lean).

The complete344384row pool has tag4 byte XOR at0, tag26 XOR3 at65536,
tag27 XOR4 at65600, tag28 XOR7 at65856 and tag29 XOR9 at82240. Every
stored row participates, and actual membership derives both operand domains,
tag isolation and exact XOR semantics. Byte literal columns equal the retained
main certificate's columns, with a different native pool offset. Only those
literal bindings reuse old results; neither whole-table identity nor worker
acceptance is assumed. Other output regions are checked over every stored row.

The strict importer retains all source bytes and validates all five regions;
calculation units preserve transparent literals. Generic finite16-element
windows are proved sound for the original block checker, with symbolic dense
array-size proofs. This split is necessary for the unchanged resource limits.
Native exporter/independent every-row/repeat-byte controls and Lean importer
controls remain separate fidelity checks from kernel semantics.

The208 actual compiled fixed queries now connect to these table roots through
the separate complete lookup-effects theorem below. No complete positive accepted worker row, initialized worker
memory/history, valid control schedule, native processing/auxiliary relation,
request-worker fulfillment/converse/accounting or unified protocol is inferred.
No main GPR/RAM frame is transported across unproved delegated actions.

## Complete local lookup effects

[Public lookup root](QueriesTheorems.lean), [Observables](Queries.lean), [Same-read query artifact](QueryArtifact.lean), [Separate intake](../../../Import/Blake2Queries.lean), [Native projection](../../../Proofs/Blake2Worker/NativeQueryProjection.lean), [Result assembly](../../../Proofs/Blake2Worker/NativeQueryResults.lean), [Regressions](../../../../Tests/NativeBlake2Queries.lean), [Intake controls](../../../../Tests/NativeBlake2QueriesImport.lean).

Complete local native acceptance on the actual fixed pool derives the exact
native tags, both operand/output domains and XOR results for every208 fixed
query, plus the2 scaled-pointer and86 timestamp-difference expression bounds.
The reference tag order is kernel-bound to the actual compiled source, never a
per-row premise. Native scalar/timestamp modeled-table scopes are unchanged.

The original worker importer is unchanged. A separate same-read observer uses
its strict parser and unchanged expression emitters. Kernel source-byte equality
and actual sublist/lookup syntax bindings connect both intakes. Pure syntax
calculations and small query units avoid evaluating witness expressions while
binding the source; generic typed getters handle assembly at default limits.
No heartbeat, recursion, memory or wall ceiling is raised.

Static native lookup counts do not measure worker issuance. Timestamp bounds
apply to differences, not raw old or processing clocks; scaled-pointer bounds
do not supply initialized read ranges. Raw ABI reads, alignment/addresses,
processing multiplicity, all43 memory/clock histories, round/reference/state/
terminal, accepted auxiliary/accumulator/caller-worker and fulfillment/converse/
accounting/protocol connections remain open. Query/scalar/clock slices are not
complete native worker witnesses, F02/F03/F04 reproductions or native defects.
