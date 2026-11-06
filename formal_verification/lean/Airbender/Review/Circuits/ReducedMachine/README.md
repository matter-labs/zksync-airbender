# Native v2 reduced machine

The active target is [NativeArtifact](NativeArtifact.lean), regenerated from the
unchanged pinned Rust. Start with its [full fixed pool](Tables/Native.lean) and
[short local theorem](Theorems.lean). Both actual sign/high-byte queries follow
from original Clean acceptance. Instruction and execution soundness remain open.
The historical intake below stays separate.

[The historical artifact](Artifact.lean) imports the pinned combined v2 JSON, with 119 equations,
eight scalar and eight timestamp lookups and six tagged lookup queries. Two tags
are native sign/high-byte ID 16; four are original witness expressions. All four
fields use the same explicit fixed setup table, following the current v3 unified
importer pattern with v2 width and coefficients. No disabled row or extra gating
is inserted. Complete source bytes and validated state/decoder/direct memory,
initialization/teardown and delegation-request coordinates are retained. The
existing shift/CSR request keeps its separate coordinates and absent ABI group;
unsupported profiles and invented ABI columns reject.

[Structural checks](../../../Proofs/ReducedMachine/ArtifactChecks.lean) live under
Proofs; [intake controls](../../../../Tests/ReducedMachineImport.lean) and
[emission controls](../../../../Tests/ReducedMachineEmission.lean) retain the
supported and rejected profiles. The complete intake checkpoint passed its bounded gates; the separate fixed-region
addition passed targeted modules/importer/exporter checks and the complete axiom
and public Review audits.

[The native sign/high-byte certificate](Tables/SignHigh.lean) checks all 65,536
literal rows of the registered ID-16 region at the actual reduced offset 196609.
[Its calculations](../../../Proofs/ReducedMachine/SignHigh.lean) stay under Proofs;
[semantic regressions](../../../../Tests/ReducedSignHigh.lean) cover byte/sign
boundaries and altered key/sign/high-byte/tag rejection. The
[strict literal importer](../../../Import/ReducedSetup.lean) validates geometry
and canonical encoding, while the kernel proves contents; parsing alone makes
no semantic assertion. [Importer controls](../../../../Tests/ReducedSignHighImport.lean)
retain that distinction. The FV-only exporter calls the unchanged registered
native table generator. No production circuit code is changed.

This historical intake supplies no execution theorem. Universal public ROM/CSR
binding, decoder membership, initialized combined history,
worker/caller accounting, physical arguments and terminal/padding boundaries
remain open. Stage-two source descriptors are opaque. Table input alone supplies
no setup correctness and cannot close a native-machine claim.
See the [current adaptation map](../../../../V3_ADAPTATION.md) and
[active plan](../../../../FORMAL_VERIFICATION_PLAN.md).

[NativeArtifact](NativeArtifact.lean) is separately regenerated from unchanged
pinned Rust and has 117 equations, 142 variables and fourteen native fixed
regions. The historical artifact has 119 equations, 141 variables and thirteen
regions. Their constraints and coverage are not assumed interchangeable.

[The full native pool](Tables/Native.lean) imports every actual tagged row and
explicit public image/CSR input of the retained fixture.
[Region/tag calculations](../../../Proofs/ReducedMachine/NativePool.lean) recover
exact sign/high-byte membership. [The short row theorem](Theorems.lean) derives
both actual constant queries from original Clean acceptance.
[Mechanical native checks](../../../Proofs/ReducedMachine/NativeArtifactChecks.lean)
retain every query and changed init/request coordinate.
[Pool regressions](../../../../Tests/NativeReducedPool.lean) and
[native/historical intake controls](../../../../Tests/NativeReducedImport.lean)
keep scope and configuration separation explicit. The
[scoped native gate](../../../../scripts/check_native_setup.py) reproduces the
compiler artifact and all fourteen regions, including changed/empty public
inputs and UNIMP padding. No production circuit code is changed.

The active claim is specific to its retained public fixed fixture. Other operation
semantics, universal public/physical setup, full decoding/history and execution
remain open. Current v3 source material does not close those v2 obligations.

The same [row theorem surface](Theorems.lean) now derives all four dynamic selector
domains from accepted native queries and the complete pool. The actual fourth
expressions remain unchanged; no row selector values are supplied. The
[absent-tag regression](../../../../Tests/NativeReducedPool.lean) rejects ID 32.
Domains do not yet identify the operation-selected tag or prove its arithmetic,
memory or CSR effect.

[Selected shift routing](Theorems.lean) now covers all six native shift-mask
cases. The [row model](Row.lean) retains the decoded-mask input and actual
observables. [Mask recovery](../../../Proofs/ReducedMachine/NativeSelectors.lean)
derives all eighteen bit bounds and the operation flags; the
[routing proof](../../../Proofs/ReducedMachine/NativeShiftRouting.lean) derives
all four tags, source-two routing and exact five-bit truncation. The
[truncation certificate](../../../Proofs/ReducedMachine/NativeTruncation.lean)
checks the actual reduced literal columns against the unchanged certified row
lemma, with distinct offsets and no equivalence premise.
[Boundary/rejection checks](../../../../Tests/NativeReducedShift.lean) include
wrong/oversized/unused fields and the distinct standalone sign-fill selector.
Public decoding still needs to supply the packed mask; initialized operands,
numerical shift/PC results and original execution remain open. The later native
port connection below derives actual contribution writes and PC selection.

[Native sign-fill results](Theorems.lean) now derive the actual filler word and
both limb bounds from the same six decoded-mask cases. All three
[minor bits](../../../Proofs/ReducedMachine/NativeShiftMinor.lean), high-limb sign,
truncated amount and fourth query are recovered. The
[128-row literal certificate](../../../Proofs/ReducedMachine/NativeSignFill.lean)
checks the native ID-20 region; [reference definitions](Tables/Shift.lean) retain
logical/positive/zero-shift behavior. [Proof assembly](../../../Proofs/ReducedMachine/NativeShiftFill.lean)
stays separate from the short Review statement.
[Eleven regressions](../../../../Tests/NativeReducedSignFill.lean) include native
shift 0/16/17/31 boundaries and altered filler rejection. Table-37 arithmetic,
full numerical results, public decoding and execution remain open. The direct
large column comparison exceeded existing resource caps and is excluded from
coverage; further work must use a smaller proof evaluation strategy.

[Native contribution and write claims](Theorems.lean) recover both actual table-37
keys/output fields, cross-limb selection, destination address and masked port write.
The outgoing PC is selected from the native default candidate; numerical successor
meaning is separate. [Actual port observables](ShiftWrite.lean) stay small;
[metadata](../../../Proofs/ReducedMachine/NativePorts.lean),
[query recovery](../../../Proofs/ReducedMachine/NativeShiftQueries.lean) and
[write assembly](../../../Proofs/ReducedMachine/NativeShiftWrite.lean) stay under
Proofs. [Eight conditional regressions](../../../../Tests/NativeReducedWrite.lean)
retain discarded lookup participation, asymmetric cross-limb contributions,
zero-shift arithmetic filler and rejected PC mismatches. They do not assert a
complete accepted witness. The decoded mask, architectural rd/x0 binding,
initialized reads, table-37 arithmetic, numeric PC+4/wraparound and original Sail
execution remain separate obligations. No new premise or circuit change bypasses them.

[Complete output-column transport](../../../Proofs/ReducedMachine/NativeShiftColumns.lean)
now covers every native ID-37 row index. Twenty small periodic-block certificates
and bounded block congruence identify the exact earlier certified column getters,
retaining swapped right outputs and the native merged zero/ascending boundary.
[Symbolic boundary reasoning](../../../Proofs/ReducedMachine/ShiftBlocks.lean)
adds no table premise. This closes the literal-column identity gap; canonical
pooled numerical row/query composition and complete results remain separate.
The combined second-output draft still exceeds the unchanged Lean allocation cap
and is excluded from source/coverage. The public row surface and native inputs
are unchanged. Decoder/source/PC/execution and protocol obligations remain open.

[Actual numerical rows](../../../Proofs/ReducedMachine/NativeShiftRows.lean) and
[full-pool numerical queries](Tables/ShiftTheorems.lean) now close the composition
gap above. Every tag-37 row has its exact key and arithmetic outputs; accepted
full-pool queries derive both 16-bit output bounds. Separate low/high getter
proofs and generic vector projections resolve the allocation failure without
changing limits, literals or native circuits. The [selected-row theorem](Theorems.lean)
now fixes both fields and bounds of each [actual contribution](ShiftContributions.lean)
at the canonical value of its actual field-packed key.
[Eleven regressions](../../../../Tests/NativeReducedNumerics.lean) retain real pool
boundary membership, output-order/carry/key rejection and discarded-write
bounds. They are not full accepted execution fixtures. Canonical architectural
source-key binding, original decoding/mask and rd/x0, initialized reads, complete
word results, numerical PC+4/wraparound and execution/protocol boundaries remain
open. No source-range, result or equivalence premise is added.

[Actual initialized clocks and logical memory history](../../Trace/Families/ReducedMachine/History.lean)
now connect this regenerated artifact's ports and clock equations to public
seed construction and accepted native matching. Newest reads and four-tick
terminal row accounting follow without supplied local clocks/order or expected
reads. Word-range preservation, source-key binding, decoding and original
execution remain separate obligations; memory consistency alone is not a
source-bound theorem. See the [native trace guide](../../Trace/Families/ReducedMachine/README.md).
