# Verification status

This is the current state, not a change log. Update it after each completed task.
**Checked** means Lean proves soundness of the imported richer no-cache constraints,
under the interfaces stated in `Review/`. It does not mean full prover/verifier soundness.
Standard instructions use pinned Sail; custom operations use the pinned project spec
or the named Clean reference. Controller claims concern explicitly modeled setup rows.
Clean is the sole constraint semantics. Fetch, interrupts and exceptions are outside scope.

## Circuit families

| Circuit | Status | Checked coverage | Remaining work |
| --- | --- | --- | --- |
| [ADD/SUB](Airbender/Review/AddSub/Theorems.lean) | Partial | ADD/ADDI/SUB/LUI/AUIPC; ADDMOD/SUBMOD/MULMOD/FMAMOD; nondeterminism writes. Destination and native register/PC effects, aliases and x0. | Nondeterminism reads need an independent oracle; delegation effects; timestamp and inactive-row interfaces. |
| [Jump/branch/SLT](Airbender/Review/JumpBranchSlt/Theorems.lean) | Partial | SLT/SLTI/SLTU/SLTIU, all six branches, JAL/JALR; native register/PC effects, wrapping, aliases and jump x0. Final-PC range discharge checked under the shared logical PC-state interface. | Bind the modeled decoder projection and active state lists to the actual setup/trace; cryptographic enforcement remains external. JALR landing-pad effects restricted to Machine mode with MLPE clear. |
| [Unsigned mul/div](Airbender/Review/MulDiv/Theorems.lean) | Checked under interfaces | MUL/MULHU/DIVU/REMU, including zero divisors; exact product/remainder relation, native register/PC effects and aliases. | Decoder, left-operand/initial-PC bounds and native reads remain interfaces. x0 reuses ADD/SUB. |
| [Shift/binop](Airbender/Review/ShiftBinop/Theorems.lean) | Checked under interfaces | XOR/OR/AND, SLL/SRL/SRA and immediate forms, REV8; native register/PC effects. Lookups derive operand/result bounds. | Decoder, operand interpretation, legal shift payloads, native reads and initial-PC interfaces. x0 reuses ADD/SUB. |
| [Word memory](Airbender/Review/WordMemory/Theorems.lean) | Partial | RAM/ROM LW and RAM SW; effective address, native register/memory/PC effects, aliases and ROM-store exclusion. | x0 loads; native memory transport/read binding and program-image interface. |
| [Subword memory](Airbender/Review/SubwordMemory/Theorems.lean) | Partial | RAM/ROM LB/LBU/LH/LHU and RAM SB/SH; native effects, signed extension, preserved bytes and PC. | x0 loads; native memory transport/read binding and program-image interface. |
| [Unified reduced machine](Airbender/Review/UnifiedReduced/Theorems.lean) | Partial | ADD/ADDI/SUB/LUI/AUIPC and TRIADD; dispatch exclusivity, native register/PC effects, aliases, x0 and carry-two wrapping. | Other arithmetic/custom, comparison/jump, shift/binop and word-memory branches; pooled-setup semantics. |
| Bigint delegation | Not started | — | Custom operation, control and request/response/memory interfaces. |
| [BLAKE2 G function](Airbender/Review/Blake2G/Theorems.lean) | Partial | Single active-row claim connects controller, both scheduled message reads, full 16-word G state update and six addresses under port/read/frame interfaces; four mixing-input bounds remain. Modeled controller update, six indices and byte addresses from imported metadata; wrap/fallback/inactive control cases. Active lane distinctness, alignment and absence of low-limb carry checked; BabyBear checked. Arithmetic proof reusable over its twenty-assertion/eighteen-query native fragment. | Instantiate the native G fragment for extended control. Global memory transport/frame, pointer bounds, eight-bit ABI domain and modeled setup binding remain explicit; full hash compression is outside the claim. |
| [BLAKE2 with extended control](Airbender/Review/Blake2Round/Theorems.lean) | Partial | 352 equations, two scaled ranges and 208 XOR queries imported into Clean. x12 high-limb range/next mask; every XOR query's bounds and exact XOR under the shared modeled setup; 128-byte state and 64-byte message alignment; first/later-round state preparation and normal/compression left/right message ordering checked. Initialization reuses Clean’s IV with Airbender’s parameter adjustments; all sixteen SIGMA-selected message words checked under an exclusive caller round mask. | Compose eight G calls and final XOR; addresses and memory effects. Round-mask exclusivity is not locally enforced; caller/ABI domain and setup provenance remain explicit. |
| Keccak special5 | Not started | — | Resolve pinned Clean's Lean 4.31 instance-registration errors before reusing its Keccak specification; lane, control and memory effects. |
| Initialization/teardown | Blocked | — | No retained equations/range queries in this artifact; needs richer proof input or a scope decision. |

## Shared and open tasks

| Task | Status / boundary |
| --- | --- |
| Shared soundness and review structure | Implemented: shared properties; `Review/` claims/interfaces, `Proofs/` proofs, `Import/` unchecked importer. Further families reuse these. Determinism intentionally removed. |
| Field generalization | Reusable prime-field lemmas implemented; artifact-dependent constants and minimum moduli explicit. BabyBear checked. Actual 128-bit artifact import/compatibility pending. |
| Decoder/register/input-bound interfaces | Open: many output bounds follow from imported lookups; remaining inputs and preprocessing must be connected to surrounding circuits. |
| [Shared PC-state ranges](Airbender/Review/PCState/Theorems.lean) | Checked under logical state matching and Clean decoder membership: covers terminal boundaries and excludes `-1` padding using the outgoing low-limb bound. Jump/branch/SLT derives that low bound from imported lookups; its malformed local row cannot satisfy this global interface. Actual decoder setup and active-row bindings remain open; cryptographic enforcement is deferred. |
| Memory transport, reads and ROM image | Open explicit interfaces; native Sail memory clauses are used, but platform transport and program-table binding are not discharged. |
| Indirect-port address interpretation | Implemented for BLAKE2 G: JSON register/scale/read/write columns imported with placement guards; shared aligned-block lemma lifts field addresses to native words. Global port enforcement and transport remain open. |
| Timestamp and inactive-row behavior | Open: local equations checked; timestamp range emission/order and global padding/state obligations incomplete. Inactive ADD/SUB rows do not locally force stuttering. |
| Fixed lookup-table provenance | Deferred: rows reconstructed from Rust, not extracted or proved bound to its setup generator. |
| Richer-to-compiled and cached equivalence | Deferred. Current soundness target is the richer JSON representation. |
| Cryptographic lookup/memory arguments and whole-machine soundness | Deferred. Logical lookup membership and explicit state interfaces are premises. |
| Completeness | Shared definition exists; no completeness theorem yet. |
| Importer and Sail generation fidelity | Trusted connections, not proved. Pins, metadata guards and importer tests expose/check parts of this boundary. |

## Machine checking

All published claims are kernel-checked. Latest integration: full Lake build,
75 importer checks, warning-as-error checks for changed modules, and an audit of
304 declarations using only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). No `sorry` or project axioms. See [reproduction commands](README.md#reproduce)
and [trust boundaries](TRUST_AND_REVIEW.md). The [plan](FORMAL_VERIFICATION_PLAN.md)
sets the implementation order; this document records the current coverage and gaps.
