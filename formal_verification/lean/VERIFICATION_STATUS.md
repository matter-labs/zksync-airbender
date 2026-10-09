# Verification status

Current state; update the tables after each completed task.
**Checked** means kernel-checked soundness of the imported richer no-cache
constraints under the interfaces in `Review/`. Standard ISA behavior comes from
pinned Sail; Clean is the sole constraint model. Logical matching, table
membership and import/generation fidelity remain explicit trust boundaries.
Interrupts, exceptions and cryptographic prover/verifier soundness are outside
these trace claims.

## Circuit families

| Circuit | Checked coverage | Remaining work |
| --- | --- | --- |
| [ADD/SUB](Airbender/Review/AddSub/Theorems.lean) | ADD/ADDI/SUB/LUI/AUIPC destination, register and PC effects; arbitrary admitted arithmetic/word-memory traces. ADDMOD/SUBMOD/MULMOD/FMAMOD local claims. Independent-stream nondeterminism in mixed traces. | Delegation effects; global inactive-row obligations. |
| [Jump/branch/SLT](Airbender/Review/JumpBranchSlt/Theorems.lean) | JAL/JALR, all six branches and four comparisons. Actual public decoding, native histories/bounds, row retirement and arbitrary family traces. | Canonical terminal PC remains a boundary; pooled-family composition. |
| [Unsigned mul/div](Airbender/Review/MulDiv/Theorems.lean) | MUL/MULHU/DIVU/REMU, including zero divisors. Actual public decoding, native histories/bounds, row retirement and arbitrary family traces. | Pooled-family composition. Discarded writes route to ADD/SUB. |
| [Shift/binop](Airbender/Review/ShiftBinop/Theorems.lean) | All standard register/immediate bitwise and shifts plus REV8. Actual public Sail decoding, native clocks/grouped register histories, derived operand/result bounds, row retirement and arbitrary family traces. | Pooled-family composition. Discarded writes route to ADD/SUB. |
| [Word memory](Airbender/Review/WordMemory/Theorems.lean) | RAM/ROM LW and RAM SW; effective addresses, native effects and selected trace composition. | Normal-path/public-image boundaries. LW-to-x0 uses the explicit Airbender NOP profile; unchanged Sail excludes that deviation. |
| [Subword memory](Airbender/Review/SubwordMemory/Theorems.lean) | Local RAM/ROM LB/LBU/LH/LHU and RAM SB/SH effects, signed extension, preserved bytes and PC. Actual public Sail decoding, native mixed ports/clocks, PC bounds, x0 preservation, source/write/terminal bounds, grouped cell histories and actual native GPR/word-RAM reads/writes. Shared original-Sail physical, checked and virtual memory transport covers bytes, halfwords and words. Arbitrary admitted RAM LB/LBU/LH/LHU/SB/SH traces now reach actual Sail retirement, terminal PC and native cell reads; all operand/address bounds and reads derive from public initialization and global history. A configured public LBU trace checks the full claim. | ROM shadow/public-byte binding and ROM-load trace composition; pooled-family composition. Discarded loads route outside this family. |
| [Unified reduced machine](Airbender/Review/UnifiedReduced/Theorems.lean) | ADD/ADDI/SUB/LUI/AUIPC and TRIADD; exclusive dispatch, native effects, aliases, x0 and carry-two wrapping. | Other selected operation branches and pooled-setup semantics. |
| [Bigint delegation](Airbender/Review/Bigint/Theorems.lean) | ADD/SUB/reversed-SUB/copy-with-carry, EQ, MUL_LOW/MUL_HIGH and overflow; native indirect addresses. Modeled setup derives source/result ranges and carry bits. | Global memory/ABI/request-response binding; RAM-only/distinct-pointer domain; exactly-one opcode and zero incoming high limb for full ABI. |
| [BLAKE2 G](Airbender/Review/Blake2G/Theorems.lean) | Active-row controller, message reads, full 16-word G update and six addresses; wrap/fallback/inactive controls. | Global memory/frame transport, pointer/ABI bounds and four mixing-input bounds; full compression. |
| [BLAKE2 extended control](Airbender/Review/Blake2Round/Theorems.lean) | One local row: preparation, SIGMA, eight G calls, final selection, chaining writes and forty byte addresses. | Global memory/frame transport, pointer/source-word bounds and caller mask/ABI; full hash call sequence. |
| [Keccak special5](Airbender/Review/Keccak/Theorems.lean) | Modeled byte relations, controls, x10 progression, indices/addresses; one theta column's five 64-bit writes match Clean. | Six other mode assemblies, D formation, schedule/column selection and full permutation; global memory/ABI. Five round bits do not enforce 24 rounds. |
| Initialization/teardown | No local soundness claim. | Blocked: artifact has no retained equations/range queries; needs richer proof input or a scope decision. |

## Shared work and open tasks

| Task | State |
| --- | --- |
| Integrated review contract | Next priority: compose the checked families through shared register/RAM history, with one small public trace contract. Existing family traces, including subword RAM, derive operand bounds and reads globally. Shared `Realizes` conclusions and native public initialization reduce repeated review declarations; composed claims come first. Pooled composition and subword ROM binding remain open; local conditional claims are secondary review material. |
| [Restricted trace](Airbender/Review/Trace/Theorems.lean) | Checked: public ADD/ADDI/SUB/LUI/AUIPC + LW/SW execution reaches native terminal PC/cell values, including the explicit discarded-load profile. |
| [External nondeterminism](Airbender/Review/Trace/NonDeterminism.lean) | Checked in arbitrary admitted mixed traces with actual CSR decoding and an independent public stream/count. Witness choices do not define the oracle. |
| Shared soundness/composition | Checked shared property definitions, row ordering, current-state source evidence, decoder framing, Sail composition and terminal last-write realization. Arithmetic/memory, jump/comparison, unsigned mul/div and shift/binop reuse these proofs. |
| Pooled native model/history | Checked six-family imported layouts with separate word/subword setups and reused clock laws. A mixed LBU→ADD fixture derives clocks and latest-write/read consistency globally; a locally valid fabricated ADD read is rejected by matching. Actual pooled public decoding is bound to the reused family projections. The shared initialized-history induction derives all six families’ read/write/terminal bounds, including cross-family operands. Actual decoder-selected x0 preservation and grouped Sail GPR/RAM histories are checked for the same pooled matching relation. Original ISA-clause retirement/composition remains open. |
| Native timestamps/state paths | Checked for arithmetic/word memory, jump/comparison, unsigned mul/div and shift/binop: four-tick advancement, strict port order, complete paths and unique access times. Subword memory also has checked native clocks and grouped histories under its public-cell image; ROM shadow transport remains open. Public initial-clock conditions remain. |
| Logical latest-write/read consistency | Checked through Clean's online-consistent history and native matching, including a six-family pooled history realized by actual Sail cell reads/writes. Public initialization supplies the seed; accepted transfers supply reads/writes. No desired-read premise. |
| Public memory/register initialization | Checked constructor reads actual Sail GPR/bytes over a distinct, aligned public domain; missing values fail. Native updates preserve public program/configuration images, including aliases. |
| Airbender boot/ROM profile | Checked zero GPR/RAM and native ROM shadow seeds, public byte binding, initial PC/clock and terminal state for the selected trace. Actual ROM bytes remain separate from shadow tokens. |
| Register/RAM value bounds | Integrated into arithmetic/word-memory, jump/comparison, unsigned mul/div and shift/binop trace soundness: public seeds, accepted writes and latest-write/read history supply operand bounds; callers do not assume them per row. Subword RAM trace soundness uses the same induction, including merged stores, and derives every operand/address bound and native read internally. The pooled six-family history also derives all input/write/terminal bounds from one public Sail image and actual decoder table; ROM shadow transport remains open. Local conditional lemmas still expose bounds internally. |
| Native PC bounds | Arithmetic/word memory, unsigned mul/div, shift/binop and subword memory range both output limbs. Jump-family intermediate PCs are bound by actual decoding/matching. |
| Jump terminal PC | Open: external terminal normalization is still required. A checked field-aliased JAL row satisfies local constraints with a noncanonical terminal PC; this is not a demonstrated whole-system bug. Teardown proof input is missing. |
| [Shared PC-state ranges](Airbender/Review/PCState/Theorems.lean) | Checked under logical matching and decoder membership, including terminal boundaries and exclusion of `-1` padding. Binding that coverage to jump teardown remains open. |
| Actual fetch/decoder binding | Checked public byte constructors invoke original Sail decoding and project native metadata for arithmetic/word memory, jump/comparison, unsigned mul/div, shift/binop and subword memory. Native binary immediate/sign-byte mapping and original clause dispatch are checked. All register/immediate/REV8 row retirement and family trace composition are checked; subword RAM retirement and trace composition are also checked. |
| Sail decoder configuration frame | Checked for the entire emitted slice: successful decoding preserves state and can replay with the same public `misa`. |
| Sail REV8 generation dependency | Closed: original Zba supplies the enablement clause needed by Zbb. Public REV8 encodings work with B enabled or disabled because the pinned platform also enables Zbkb. Pins unchanged. |
| Direct native ports/word representation | Zero, two-limb and four-byte forms imported with placement guards. Byte packing matches Rust's field arithmetic; checked bounds recover RV32 bytes. Shift amounts need only the low two source bytes; the review mapping omits unused high bytes. |
| Indirect-port address interpretation | Checked metadata/aligned-block connections for both BLAKE2 families, bigint and Keccak. Global enforcement, memory transport and ABI binding remain open. |
| Native Sail memory transport | Checked shift/binop native GPR reads/writes and x0 tokens, subword mixed GPR/word-RAM port transfers, shared byte/halfword/word physical, checked and virtual memory transfers, PMA/PMP/MMIO checks and missing-byte failures, GPR/RAM writes, byte reads, frame/code preservation and original LW/SW execution, including Machine translation, access checks, PMP/PMA and failure propagation within the reviewed configuration. |
| Discarded LW semantics | Explicit deviation: an accepted native NOP can differ from original Sail under sparse memory. `NoDiscardedLoads` restricts the original-Sail claim; the named Airbender profile covers native discarded loads. |
| Field generalization | Reusable prime-field proofs; minimum moduli and serialized inverse conditions explicit. BabyBear checked. Native 128-bit artifact coefficients and some BLAKE2/bigint constants still need coverage. |
| Inactive rows | Open global padding/state obligations; selected traces bind active rows. Inactive ADD/SUB rows do not locally force stuttering. |
| Fixed-table extraction/provenance | Deferred. Current rows are modeled from Rust, without an extracted artifact or proved setup-generator binding. |
| Richer-to-compiled/cached equivalence | Deferred. Current proof target remains the richer imported representation. |
| Cryptographic lookup/memory enforcement | Deferred. Logical membership/permutation premises are explicit. Whole-machine prover/verifier soundness is not claimed. |
| Completeness | Shared definition exists; no completeness theorem. |
| Importer/Sail generation fidelity | Trusted, not proved. Pins, provenance hashes, metadata guards and regression fixtures check parts of this connection. |

## Machine checking

The full-family baseline has **98 importer checks and 578 audited declarations**;
the focused trace targets have **33 importer guards and 878 audited declarations**.
Accepted and rejected fixtures exercise aliases, public decoding/configuration,
clocks/rollover, native histories, memory transport and actual Sail retirement.
Changed project modules pass warning-as-error checks. Audits allow only
`propext`, `Classical.choice` and `Quot.sound`; no `sorry` or project axioms.

See [reproduction commands](README.md#reproduce), [trust boundaries](TRUST_AND_REVIEW.md)
and the [plan](FORMAL_VERIFICATION_PLAN.md) for details.
