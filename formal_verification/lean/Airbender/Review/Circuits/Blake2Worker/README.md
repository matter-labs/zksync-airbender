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
uninterpreted. The four-field lookup setup is modeled; actual worker fixed-table
certification is still pending. Existing main-circuit intake remains fail closed.

Positive control slices cover only16 actual equations, including zero and
multiple round flags. They do not establish complete native acceptance, valid
round scheduling, v3F02/F03/F04 reproduction or a defect. Native fixed tables,
ABI alignment/addresses/ranges, processing flags/clocks, full memory matching,
reference state/round effects, issued/unissued request/auxiliary/accumulator
connections, fulfillment/converse/accounting/terminal/protocol remain open.
General compiler/Rust/JSON/physical/field/LDE/crypto/completeness boundaries and
main CSR/MOP execution are unchanged. No native production code is modified.
