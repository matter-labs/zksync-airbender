# Trust and review boundaries

**Review definitions and assumptions for meaning; let Lean check the proofs.**
The kernel checks proofs about emitted objects. It does not establish that those
objects faithfully represent Rust artifacts or express the intended system claim.
[Verification status](VERIFICATION_STATUS.md) is the coverage and gap inventory;
[the plan](FORMAL_VERIFICATION_PLAN.md) contains pending work.

## Review entry points

Start with [Trace/Soundness.lean](Airbender/Review/Trace/Soundness.lean), then
[pooled public inputs](Airbender/Review/Trace/PooledExecution.lean),
[native matching](Airbender/Review/Trace/Model.lean), the
[family registry](Airbender/Review/Trace/Pooled.lean), and
[actual public decoding](Airbender/Review/Trace/PooledProgram.lean).
[Execution.lean](Airbender/Review/Trace/Execution.lean) states the shared `Realizes`
conclusion; [SailHistory.lean](Airbender/Review/Trace/SailHistory.lean) defines native
row events and the meaning of intermediate and retired states.

`Review/` contains references, artifact selection, named word/port mappings,
properties, public assumptions and primary claims. `Proofs/` contains supporting
calculations, interfaces, proof assembly and artifact guards. Review `Import/`
separately for fidelity. Per-circuit `circuitModel` and `InterfaceAssumptions`
remain visible; accepted row membership supplies that row's imported constraints.
Shared initialized history derives bounds, actual reads and preprocessing.
[RowPosition](Airbender/Review/Trace/RowContext.lean) applies earlier native writes
without assuming successful reads or ISA execution.

Unified models and workers retain their own explicit public contracts. For their
claims and remaining scope, use the status table rather than inferring whole-machine
coverage from a local operation theorem.

## Sources and pins

| Component | Source and review obligation |
| --- | --- |
| Lean kernel and standard axioms | Accepted proof-checking foundation. The [axiom audit](Airbender/Checks/Axioms.lean) records actual dependencies. |
| Lean / Mathlib | `v4.31.0`, pinned in `lean-toolchain` and [lakefile.toml](lakefile.toml). |
| Clean | `1e563b9c27991b3795eb440c1ee0757edb4ce8b1`; upstream definitions in `.lake/packages/Clean`. Review their applicability; Lean checks proof terms. |
| Clean compatibility preparation | [prepare_clean.py](scripts/prepare_clean.py) guards original hashes and lists tactic-import, factory-registration and proof-reduction patches. Constraint semantics, algorithms and theorem statements are unchanged; repaired proofs are checked and audited. |
| Sail model/compiler | Pinned source in `vendor/sail-riscv`; exact pins, source hashes and generation details in [provenance](generated/sail-rv32/provenance.json) and [regeneration notes](generated/sail-rv32/README.md). |
| Sail runtime | `lean-sail` revision `c816ea7ad03cce98d51acee252540fd4215fede8`, pinned in `lakefile.toml`. |
| Platform support | [SailPlatform.lean](scripts/SailPlatform.lean), copied by the original backend. Experimental extensions are disabled to match the pinned emulator configuration. Runtime compatibility is proved in [Runtime.lean](Airbender/Proofs/Sail/Runtime.lean); terminal/reservation calls remain abstract parameters. |
| Project profile/custom reference | Unmodified [00-master.md](vendor/airbender/00-master.md) at `2331d1c511f26c17be85879fbab02ab109aefd05`, with [hash/provenance](vendor/airbender/provenance.json). Applicability to the circuit revision remains a review obligation. |
| Base ADD/SUB artifact | `av_gkr_compiler` revision `28ffe3ff0353edd9051485c2974b28b52b495dc4`; [retained no-cache JSON](../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json), SHA-256 `084a58f08dd122160b548689383f74d4a790c782046f8a5bf43f9f287c22a620`. Other family JSON paths remain in their reviewed artifact declarations. |

## Import and generation fidelity

Clean supplies `Expression`, `FlatOperation`, `Environment`, static tables and
`ConstraintsHoldFlat` directly. The JSON schema is parser data, not a second
arithmetic semantics. Audit [Parse](Airbender/Import/Parse.lean),
[Schema](Airbender/Import/Schema.lean),
[Coefficients](Airbender/Import/Coefficients.lean) and
[Embed](Airbender/Import/Embed.lean). Coefficient cast equivalence is proved, but
faithful parsing/emission is not. Placement guards reject missing or ambiguous
logical variables and check memory/witness banks. Named imported descriptors do
not prove that Rust preprocessing or decoder-table contents match the model.

The target remains the richer no-cache representation. Compiled-gate implication,
witness extension and cached-layout equivalence are unproved. Generic prime-field
claims retain their stated minimum moduli and inverse compatibility; they do not
establish import of the native Proth120 artifact with its own coefficients.

Sail standard instructions call original generated clauses, with no replacement
arithmetic specification. Review [generate_sail.py](scripts/generate_sail.py),
[sail_slice.ml](scripts/sail_slice.ml) and the recorded provenance. The generator
extracts the unique normal `F_Base` nextPC assignment verbatim from pinned
`run_hart_active` into `extracted_base_pc.sail`, then compiles it with Sail.
Hashes identify inputs and outputs; extraction, compilation and pruning fidelity
are not proved. The selected successful four-byte path does not include the full
fetch driver, interrupts or exceptional branches. `MemoryPlatform` externals are
abstract conditions, without supplied implementations or project axioms.

Public decoder constructors use actual Sail byte reads and original decoding.
The restricted pure and M-extension interpreter constructors preserve their
configuration requirements, including `misa`; checked frame proofs transport
source evidence through history. The native metadata projection still needs
review against Rust. Custom CSR/Zimop behavior comes from the pinned project
reference and explicit reviewed clauses rather than standard CSR execution.

## Modeled tables and logical arguments

[RangeChecks.lean](Airbender/Review/RangeChecks.lean) enumerates 16-bit limbs using
Clean's `StaticTable`; membership characterization is kernel checked. Its rows
reconstruct [Rust range setup](../../prover/src/gkr/virtual_polys/range_check.rs),
selected with 16 bits in [the prover](../../prover/src/gkr/prover/mod.rs).
The 19-bit timestamp table and worker controller/XOR/operation tables have the
same unproved setup-generator correspondence. Exact extracted rows, table identity,
query binding and padding remain deferred provenance work.

`Accepted` checks imported equations/lookups and logical native state/memory
permutations. Decoder membership and caller/request matching are likewise logical
conditions. [Caller request windows](Airbender/Review/Delegation/RequestHashWindows.lean)
reuse these checks at aligned instruction cuts after clock two. Exact worker/caller
multiplicity, slots and full CSR families are derived; zero-clock worker effects
stay in the actual prefix. Hash-window claims retain explicit worker-only memory
matching and protocol ABI; joint mixed retirement and control preparation remain
open. Native columns retain full address/time/value limbs, including readonly
clock refreshes. Bounds, latest-write reads and Clean online-consistent histories
are derived from those relations and public initialization. Retiming introduces
initialization writes and preserves addresses/values; it does not prove cryptographic
permutation or lookup enforcement. Prover/verifier refinement and protocol soundness
are separate obligations.

## Public state, profiles and external inputs

[InitialImage.lean](Airbender/Review/Trace/InitialImage.lean) reads actual Sail GPRs
and bytes over a distinct public cell domain; missing cells fail. Public inputs
bind initial PC/clock, configuration, program bytes and modeled ROM. Relevant
memory claims retain alignment, ordinary-address/domain and platform conditions.
Per-row expected reads, operand bounds and execution results are conclusions.

The [initialization profile](Airbender/Review/Trace/Initialization.lean) fixes zero
GPR/non-ROM RAM and PC zero. [NativeMemory.lean](Airbender/Review/Trace/NativeMemory.lean)
keeps zero native ROM shadow slots separate from public code bytes. Slot masking
comes from `mask_read_for_witness` in `riscv_transpiler/src/replayer/mod.rs`;
zero seeds come from `inits_or_teardowns_as_flattened_relation` in
`prover/src/gkr/prover/forward_loop/utils.rs`. Checked public-byte view conversions
preserve the relevant constraints, queries, ports, clocks, outputs and matching.
[Unified NativeROM.lean](Airbender/Review/UnifiedReduced/NativeROM.lean) exposes its
projection explicitly. Rust fidelity and cryptographic enforcement remain external;
worker ROM transport retains the gap recorded in the status table.

The unchanged-Sail theorem retains `NoDiscardedLoads`: an accepted native NOP
can fail an actual Sail load under sparse memory, as
[DiscardedLoad.lean](Tests/DiscardedLoad.lean) checks. The named Airbender
`profileClause` implements the pinned LW-to-x0 PC-only-NOP rule through Sail's
ADDI x0,x0,0 clause. Keep that profile connection distinct from original LOAD
semantics. Arithmetic writes to x0 use their original clauses.

[NonDeterminism.lean](Airbender/Review/Trace/NonDeterminism.lean) receives an external
stream independently of the witness. `StreamPorts` explicitly connects native
response ports; the circuit does not authenticate a fixed stream and permits
different responses. Native clocks derive positions, and the execution claim
concludes the exact consumed count. Hints consume no word and make no application
I/O claim. Native ROM views must preserve this input connection.

The selected claims retain normal-path/configuration, field and terminal boundaries.
Checked surplus-worker, bigint-control and ROM-shadow counterexamples must stay
visible at their actual logical scope; no whole-system exploit, circuit fix or
assumed ABI validity follows. Use [Verification status](VERIFICATION_STATUS.md)
for those fixtures and all unresolved coverage, and
[the plan](FORMAL_VERIFICATION_PLAN.md#deferred-milestones) for downstream proofs.
