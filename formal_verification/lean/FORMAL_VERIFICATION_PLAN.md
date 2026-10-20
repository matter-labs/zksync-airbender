# Circuit formal verification plan

Backport the current formalization to Airbender v2 on dev while preserving its
small review surface, directory roles, pinned references and explicit trust
boundaries. This document is a snapshot of pending work; checked coverage lives
in [Verification status](VERIFICATION_STATUS.md), and accepted counterexamples
and unresolved connections live in [Findings](FINDINGS.md).

## Integrated review contract

Keep the same ownership boundaries as the source formalization:

- Review/Circuits owns selected references, artifacts, observable mappings and short public claims.
- Review/Helpers owns common properties, word representations, tables and local context.
- Review/Trace owns whole-execution and terminal-state contracts.
- Proofs owns calculations, selector recovery, native-equation checks and composition.
- Import owns the separate artifact-fidelity boundary.

Use original Clean constraint semantics and original pinned Sail standard clauses.
Reuse shared proofs unchanged when possible; record adaptations explicitly.
Derive local selectors, bounds and actual reads before promoting a row claim to
an initialized trace claim. Never hide a result or desired intermediate state in
an interface. Keep public assumptions visible and v2 findings independent.

## Continuing execution

The user authorized hourly continuation and regular commits on 17 October 2026.
The active schedule is Continue Airbender v2 formal verification backport, attached
to this backport chat. Keep working in the isolated dev-based worktree and commit
small verified milestones with Conventional Commits. Do not push without authorization.
Use the [serial bounded verification runner](scripts/check_all.py) and its
[validated watchdog](scripts/bounded_fv.py): one Lean worker, Lean memory cap
3072 MiB, total footprint at most 3072 MiB, resident at most 4096 MiB and finite
wall budgets. Confirm termination after limits and redesign instead of raising caps.
The original v3 schedule remains separate and paused.

## Pending integration work

Native direct shuffle-RAM/state metadata, ADD/SUB clock extraction and initialized
logical memory histories are checked. Accepted state/memory matching and initial
clock boundaries now derive all row/prior clock inputs, complete Clean memory
consistency and newest preceding reads. Public Sail image construction now binds
seed tokens and initial PC to actual reads, deriving initial bounds/clocks and
unique addresses. Ten-column native decoder placement/query order is checked,
including the separate zero flag. Selected-profile public Sail setup construction,
full padded logical membership, native padding exclusion and recovered zero flags
are checked. Initialized history now derives native read/write/terminal bounds;
canonical decoder PC/immediate and register-index bounds are checked. Native history
now constructs actual Sail reads/writes and intermediate states, including x0
preservation from v2 masked writes. Derived clock order groups complete rows;
readonly refreshes preserve the instruction pre-state even with aliases. Public
indexed PCs now derive every incoming PC alignment, including RV32 truncation.
Native equations derive bounded outgoing successors, and state matching bounds the
terminal PC. The proof layer now assembles all five arithmetic row interfaces
and original Sail preparation/execution/retirement from these derived facts and
actual native history. Rebased control transport derives PC reads and reaches the
actual masked write. Complete initialized five-opcode execution now composes
original Sail byte reads/decoding and normal steps to exact terminal PC/cells,
including empty traces. Native GPR metadata preserves all code bytes; actual pure
decoder evidence is retained from construction. A reversed two-row ADD/ADDI
witness derives PC 8 and x2=247 with no intermediate/result premise.

1. Finish binding native word-memory alongside checked arithmetic execution.
   All v2 equations/queries/metadata and native-shaped ROM tables now support
   checked transfer laws, alignment, exact ROM values and RAM-only stores.
   Native address arithmetic, modular PC successors and clock/port laws are also
   checked under explicit source/immediate/initial-PC and clock inputs.
   Public LW/SW decoding is now checked in a separate native registry: complete
   padded membership recovers actual original Sail source evidence, exact zero
   flags and PC/immediate bounds/alignment, including original x0 loads.
   Actual Sail byte extraction now binds native ROM data inside the public
   prefix; a complete four-MiB extraction covers every native ROM address.
   Initialized logical word-memory history now reuses shared matching, native
   clock recovery and decreasing-time range induction. Public seed construction
   derives all initial/per-row/prior clock inputs and all read/write/terminal
   word bounds, including discarded ROM-shadow reads; full decoder membership
   supplies the zero flag. Nonempty LW/SW/x0 fixtures and omitted-shadow rejection
   are checked. Initialized native-row assembly now derives effective-address
   addition, bounded aligned PCs, modular successors and clock/port order using
   existing native calculations unchanged, with no per-row numerical premises.
   Actual Sail cell realization and native row grouping are now checked with
   mixed-port x0 preservation, source-GPR transport and actual register/RAM writes.
   Reversed dependent store/load rows derive the intermediate RAM state and later
   read without a supplied state/read result. This realizes the full supplied
   native image, including shadow cells tracked as RAM. Native shadow accesses
   below four MiB now provably preserve their exact read value; native matching
   still retains every refresh token. Whole-address projection now preserves
   Clean consistency/latest writes and realizes only architectural cells in Sail.
   A separate public initializer reads architectural cells and retains canonical
   native shadow seeds independently; clocks, unique addresses, x0 preservation
   and complete row grouping are derived. The same constructor now supplies
   canonical seed bounds to the unchanged shared range induction, deriving all
   full native read/write/terminal ranges, including erased shadows. Ordinary/x0 ROM-load regressions retain
   full matching and actual masked Sail writes with unreadable shadow locations
   and distinct native shadow/ROM values. Projected initialization and public
   decoding now derive effective-address addition, bounded aligned PCs, modular
   successors and native clock/port effects through the existing calculations.
   Shared readonly-prefix transport recovers every retained port read in the
   instruction pre-state and the final actual masked write; native constraints
   prove that the final port always survives projection. Ordinary/x0 ROM loads
   and reversed dependent RAM store/load rows exercise these interfaces without
   supplied reads/intermediate states. Projected transfers now preserve every
   byte below four MiB, including missing bytes and code outside the tracked
   domain. Actual RAM writes remain outside that region. Successful public ROM
   extractions survive every projected prefix; public setup construction derives
   complete code-byte windows for programs fitting the native ROM region, and
   original Sail source/decoding evidence survives. A reversed dependent SW/LW
   regression simultaneously derives a real RAM change, retained ROM extraction
   and original code evidence without a later-read/result premise. Eight unchanged
   pinned Sail platform modules now discharge Machine translation, PMP/PMA and
   ordinary-memory helpers under public configuration. Actual projected native
   histories preserve that configuration. Native RAM reads/writes and alignment
   now feed original virtual-memory calls; the same reversed dependent SW/LW
   fixture derives a real virtual store and subsequent load without expected
   intermediate/read/state premises. Actual public ROM extraction and preserved
   prefixes now feed original Sail virtual ROM loads. Native address bounds derive
   their ordinary-address domain. Native masked writes now match the original LW
   destination effect, including x0 without NOP projection; the proof layer reaches
   the original ROM LW clause result in the actual native after-state. Ordinary/x0
   initialized fixtures construct actual ROM/decoder bytes and configuration while
   retaining shadow value 123 distinct from the loaded ROM word 0xc0001073.
   Original RAM LW/SW clauses now reach the actual native cell-transfer states.
   Native decoder fields derive opcode selectors, original registers and sign
   extension; retained native ports derive rs2 and RAM reads, including masked
   load writes/x0. The same reversed dependent fixture reaches original SW then
   LW clause results with actual read 123 and the actual destination write,
   without a supplied intermediate state/read or desired result. Original Sail
   nextPC preparation and PC retirement now compose all three RAM/ROM clause
   paths through unchanged control/history/configuration lemmas. Actual decoding
   selects original LW/SW; initialized effects derive the effective address and
   exact modular native PC successor. The small original Sail dispatcher is
   reused without v3's discarded-load profile. Ordinary/x0 ROM fixtures retire
   to native PC 4, and the same reversed SW/LW fixture reaches actual PC 8 and
   terminal RAM/x3 values 123 without intermediate/read/PC/result premises.
   [General initialized word-memory execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
   now composes every derived row through actual code reads, original decoding
   and normal preparation/clause/retirement. Public cell and shadow-seed domains
   discharge all local ordinary-RAM and actual ROM-prefix coverage conditions.
   Projected composition retains every native shadow token in matching and
   concludes the exact terminal PC and architectural cells, without equating
   shadow values with actual ROM bytes. The reversed dependent SW/LW fixture
   reaches PC 8 and RAM/x3=123 through this general relation; ordinary/x0 ROM
   loads and empty traces also pass. Configuration, public program size in ROM,
   ordinary public RAM and actual ROM extraction/seed coverage remain visible.
   [Fixed native zero boot](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
   now uses the unchanged original Sail initial profile and boot-image proof.
   Public domain geometry and native zero GPR/RAM/shadow seeds derive the general
   initialized execution boundary. Complete native paths keep terminal shadow
   values zero independently of actual ROM bytes. Ordinary/x0 boot fixtures reach
   native PC four and actual destination values; invented native seeds and
   nonzero public GPRs are rejected. The native proving-loader padding path was
   retested: it zero-extends the input words to four MiB, while the raw table
   constructor uses UNIMP only outside the image it receives. The separate
   [padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean) now proves
   full extent, unchanged prefix and zero tail symbolically. The explicit
   [loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) now
   pads actual Sail byte memory and derives complete four-MiB ROM extraction.
   Symbolic lookup/word-vector proofs avoid evaluating a huge map or list.
   Prefix bytes, ordinary RAM, registers, the original zero profile and public
   Machine/PMP/PMA configuration are preserved. Actual public decoder setup
   survives when its code lies in the supplied prefix. The small padded-boot
   claim now derives every shadow coverage condition from construction and the
   existing public ROM domain. Ordinary/x0 native fixtures pass complete original
   execution from that padded state; missing/oversized prefixes reject padding.
   Physical setup geometry is now imported and guarded for both artifacts:
   exact 12/16-column placement, ten-wide decoder groups, four-wide tagged tuples,
   complete table offsets, decoder capacity and the reserved normalization row.
   The [active setup-row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
   retains native dummy/zero-padding tuples and tags 23/24. Symbolic proofs derive
   exactly the existing logical ROM/separator membership from these tuples;
   tagged ROM membership then derives actual Sail reads after the public loader.
   Nonempty real-byte fixtures check original/padded reads and altered-word/tag
   rejection. The [standalone native exporter](../native_setup_exporter/README.md)
   now emits actual regional generic/decoder/range16 values and public image/text
   data without building a full trace. The pinned LW/SW/x0/UNIMP fixture has exact
   reproduction, exhaustive lossless compression checks and symbolic certificates
   for every ROM/separator/range row, unsupported decoder slot and image zero tail.
   Its actual tagged ROM rows feed original Sail reads through the existing loader.
   [Sparse public construction](Airbender/Review/Helpers/Decoder/SparseSetup.lean)
   now retains unsupported pure words at indexed PCs and rejects missing/effectful
   inputs. Native mask equations exclude holes/tail before source recovery and
   derive canonical words/alignment and the exact zero flag. A second actual native
   export has an interior UNIMP slot: supported PCs stay 0/8/12. Actual original
   Sail reads/decoding construct its sparse setup, and every exported decoder row
   is certified against it. A complete native x0-load row at PC 12 satisfies all
   original equations/lookups and recovers its actual public source. No table
   equivalence is a premise. [Sparse initialized execution](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean)
   now shares the existing native history, numerical, code-frame, original Sail
   clause/retirement and terminal assembly. Actual strict/sparse constructors
   derive proof-internal indexed source evidence; the strict public claim is
   unchanged. A nonempty fully initialized x0-load fixture selects actual exported
   slot three and derives original execution from public PC 12 to PC 16, RAM 123
   and x0 zero. The PC-four hole remains in actual public bytes; no step through
   an unsupported instruction or control-flow skip is claimed. No per-row read,
   intermediate state/result or table-equivalence premise is supplied.
   [Shared native scalar export](Airbender/Review/Helpers/Tables/NativeScalars.lean)
   now certifies every range16/timestamp19 prefix value and source-shaped active
   zero filler. The timestamp generation clause is copied unchanged from pinned
   native source with its existing constant; no full prover build is needed.
   Exact lookup meanings connect to the unchanged Clean helpers. Both compiled
   scalar placements, endpoints/padding and fourteen strict importer checks pass;
   the reserved normalization row and physical multiplicity enforcement remain
   outside this model. The [actual arithmetic export](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean)
   now certifies all 1,048,576 native ten-column slots against independent public
   bytes and original Sail sparse construction. The seven-word fixture covers
   all five arithmetic opcodes, signed ADDI, original SUB-to-x0, raw U-type funct3,
   an interior UNIMP hole and ADD at original PC 24. Native packed-mask equations
   exclude holes/tail; a complete post-hole ADD row recovers its actual source.
   Exact fixture/binary reproduction and nineteen strict importer checks pass.
   No table-equivalence premise or custom MOP coverage is added.
   [Sparse initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean)
   now shares the existing numerical/native history/original Sail/terminal
   assembly through proof-internal indexed evidence derived from either builder.
   The strict public theorem statement is unchanged; complete sparse membership
   excludes holes/tail before source selection. A fully initialized nonempty ADD
   fixture uses actual exported slot six at original PC 24 and derives fetched
   execution to PC 28 and x1=246. Full alias matching derives every refresh/read;
   no indexed-source, per-row bound/read, intermediate state/result or table
   equivalence is a public premise. The PC-20 UNIMP hole remains public bytes;
   initial PC 24 is supplied, with no control-flow skip asserted.
   [Active decoder rows](Airbender/Review/Helpers/Tables/NativeDecoder.lean)
   now retain each of the three actual native prefixes and the direct native
   padding API output throughout the remaining 15,728,639 active rows. Literal
   minus-one padding is already present in every prefix, so symbolic proofs
   derive exact membership without a table-equivalence premise. Compiled column
   positions 2/6, native capacity and active boundaries are checked. The short
   [arithmetic bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean)
   derives initialized execution from this full active decoder domain; the same
   real alias fixture reaches PC 28/x1=246. No huge trace allocation or finite
   domain enumeration is used. Native source comments mentioning zeros do not
   replace actual sentinel data. Reserved c0 normalization and Rust full-trace/
   LDE/argument refinement remain separate. Next generalize exported-data
   certificates to arbitrary public programs and bind full physical trace
   assembly/initialization.
   [Complete active setup rows](Airbender/Review/Helpers/Tables/NativeRowsData.lean)
   now assemble all scalar/generic/decoder columns, with exact imported placement
   and unchanged Clean scalar/fixed-table membership derived in Proofs. Full
   windows reject truncation; arithmetic has no generic group. Decoder filler can
   overlap still-active tagged ROM data, and last active rows retain distinct
   scalar/generic zero and decoder minus-one fillers. The initialized arithmetic
   alias regression now consumes complete-row decoder columns and derives the
   same PC 28/x1=246. Next refine this row model against Rust trace construction
   and generalize native decoder certificates; normalization/LDE, multiplicities
   and cryptographic enforcement stay separate.
   The fixture certificates are not general Rust/export/LDE/compiler refinement.
   Rust refinement and cryptographic enforcement remain separate.
   Preserve v2 PC rollover and native timestamp offsets;
   keep physical setup generation/export and mixed/custom expansion explicit.
2. Add native jump/branch/SLT and extend the shared execution relation with checked
   control-flow interfaces. Preserve full native setup padding and actual public
   code-byte/decoder evidence; do not add per-row result or PC premises.
   [The concrete native artifact](Airbender/Review/Circuits/JumpBranchSlt/Artifact.lean)
   and both fixed tables are now checked: all 36 equations, 16 lookups and exact
   typed metadata; [actual native export](artifacts/setup/jump-control-native.json)
   has cleanup/conditional tags 17/43 and offsets 0/65536 without a dummy row.
   Symbolic/small finite certificates derive exact membership and fixed effects.
   The full active JAL witness, wrong targets/profiles, signed/unsigned flags,
   changed outputs and actual JAL alignment rejection pass. The v2 conditional
   table keeps flags and funct3 separate. [Native PC bounds](Airbender/Proofs/JumpBranchSlt/PC.lean)
   now follow from all constraints and supported masks: outgoing high equals
   scalar-ranged variable 43, and outgoing low is the raw or cleaned ranged key.
   The JAL -4 field-minus-one variant passes all polynomials and the other 15
   queries but fails actual scalar query index 5; the canonical target passes.
   Do not copy the v3 F01 closure premise into this local claim.
   [Public control decoding](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean)
   now constructs actual original Sail bytes/metadata and full sparse padding;
   native packed-mask bounds exclude sentinels and recover the supported mask,
   canonical words/alignment and exact x0 flag. The public claim derives PC
   bounds without a supplied mask. Retain v2 SLTI mask 8, branch mask 16, original
   x0 operations and raw JAL funct3 (tag 7 for -4). The full public JAL witness
   passes; wrong tag-zero membership and the malformed high PC reject.
   [The actual native control decoder export](artifacts/setup/jump-decoder-native.json)
   is now certified against independently constructed public Sail data, preserving
   raw JAL tag 7, the interior hole and original SLTIU-to-x0 at PC 8. Every prefix/
   tail row is proved equal using the arithmetic certificate structure, and the
   short exported-decoder claim derives source evidence/PC bounds from actual
   membership plus all native constraints. Both binary/fixture modes reproduce;
   crossed/unsigned-only profiles, malformed inputs and tag-zero membership fail.
   [Native control clocks/ports](Airbender/Review/Helpers/Context/JumpBranchSlt.lean)
   now discharge the unchanged shared clock/history contract, using actual native
   carry/borrow equations and all eight timestamp queries. [The short public history
   claim](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) derives complete
   Clean history and newest reads from actual public Sail seeds/PC plus full native
   matching. The accepted JAL -4 fixture retains both aliased x0 refreshes and the
   actual link write; stale local reads fail matching. Missing register data,
   19-bit lower-clock carry, derived port effects and terminal clocks are checked.
   [Control word bounds](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean)
   now follow from actual public sparse decoding, native write equations and
   unchanged initialized range induction, including all readonly aliases and
   terminal tokens. [Hardwired-x0 preservation and Sail cell history](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean)
   reuse native destination masks, shared zero-value induction and row grouping
   to derive actual cell transfers/intermediate states. The exported JAL fixture
   checks old x1=123 to actual link four with both x0 refreshes retained.
   [Original control register accesses](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean)
   are now connected to the derived native history: unchanged readonly-prefix
   transport and decoded indices recover both source reads, the old destination
   read and actual masked write in one cell-history pre-state. Shared append/split
   proofs derive every row's actual segment states and original public source
   entry, without a per-row state/read/schedule premise. The exported JAL fixture
   derives both x0 reads, old x1=123 and link write four through the public claim.
   [Saved JAL/JALR links](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
   now follow from native carry equations 29/30, actual scalar ranges and shared
   modular word addition. Full public decoding supplies PC bounds and the x0 flag;
   native packed masks one/two recover all selectors before actual masked writes.
   The exported JAL, new logical JALR/x0 cases, full local native PC+4 wrap and
   altered-link rejection are checked. The wrap row is not a public-decoder or
   initialized execution certificate, and the new logical fixture has no new
   native arbitrary-program export certificate.
   [Native jump targets](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean)
   now derive actual JAL/JALR PC sums, JALR bit-zero clearing and four-byte
   alignment from initialized matching and original public byte decoding. Shared
   history supplies indirect-source ranges; unchanged original Sail decoder lemmas
   and native metadata supply JAL parity. Actual native high-candidate range
   queries eliminate the v3 final-high closure interface. The exported negative
   JAL and a new initialized aliasing JALR (public x1=257, odd sum 265, target 264)
   pass, with local x0/wrap and bit-one rejection cases. Logical-fixture native
   export and initialized wrap execution are not claimed.
   [Initialized comparison results](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean)
   now derive actual SLT/SLTU/SLTI/SLTIU masked writes from native subtraction,
   positive high-limb flags, actual scalar/fixed queries and initialized matching.
   Public original decoding derives register/immediate identity, signedness and
   x0; no sign/borrow bit, operand bound, expected read or result is supplied.
   Unchanged original signed word-ordering lemmas are reused. Four separately
   initialized cases cover signed/unsigned disagreement, sign-extended -1,
   discarded true SLTIU-to-x0 and its readonly alias refresh. Its query also occurs
   in the prior native export; new logical-program export is not claimed.
   [Comparison PC advancement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean)
   now follows from actual native candidate/routing equations, Boolean carries
   and both scalar bounds, retaining RV32 wrap. Public decoding derives incoming
   ranges/alignment and exact comparison selection; no register-image boundary
   or per-row PC/carry/result is required. All four initialized fixtures pass;
   full native wrap and altered-PC rejection are local regressions, not a new
   initialized wrap execution or native export certificate.
   [Initialized branch conditions](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean)
   now derive all six predicates, taken/complement bits and actual zero writes.
   Original subtraction, signed ordering and the unchanged positive-high proof
   are reused; actual inverse equations identify equality, while scalar/fixed
   queries resolve signs and borrow. Public original metadata derives mask/tag
   identity and complete matching supplies both operand ranges. Eighteen
   initialized cases cover both outcomes per opcode, opposite signed/unsigned
   orderings and equality. A false equality/table answer fails the native inverse
   equation; no new defect or native program-export certificate is claimed.
   [Initialized branch targets](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean)
   now follow the checked decisions to PC+offset or PC+4, retaining RV32 wrap and
   four-byte alignment. Original decoder/sign-extension lemmas derive offset
   parity; public metadata derives PC/offset ranges, alignment and selectors.
   Native carries, both scalar candidate queries and taken-only bit-one checks
   derive exact outgoing words, with no final-high closure premise. All eighteen
   initialized cases pass; local taken -4, taken/untaken wrap and misalignment
   rejection are separately checked without claiming initialized wrap execution
   or a new native export certificate.
   [Original comparison clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
   now execute SLT/SLTU/SLTI/SLTIU in constructed initialized-history segments.
   All operand/result/immediate/PC inputs come from native matching and original
   public decoding. Unchanged Sail clause, preparation, history-frame and
   retirement proofs are reused; native x0 handling and both candidate bounds
   remove the source nonzero-destination/final-high interfaces. The four existing
   original-byte fixtures execute from actual public states; true SLTIU-to-x0
   retains x1=123 and data stuttering while retiring PC eight to twelve.
   [Original branch clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean)
   now connect all six predicates/targets to original BTYPE clauses in constructed
   segments. Native matching and public decoding derive all reads, bounds,
   offsets, conditions and PCs. An actual initial misa entry is explicit, with
   unrestricted value; unchanged original CSR frame lemmas transport it through
   history. All eighteen native fixtures are reused unchanged and execute both
   outcomes per opcode with that public CSR entry, deriving full data stuttering.
   Missing-entry/accessor regressions retain this original-state boundary.
   [Original JAL/JALR clauses and retirement](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean)
   now reuse unchanged pure definitions and the complete original retirement
   declaration. Native links, targets, actual reads/writes and public constructors
   derive all row interfaces. Initial misa is readable; only traces containing
   JALR need actual Machine privilege and MLPE-clear mseccfg. Unchanged history
   transports the profile. Existing negative JAL and aliasing JALR fixtures
   execute original retirement and the exact native link write in the same
   constructed after-state; JAL has no privilege/security entries.
   [Complete fetched control execution](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean)
   now reuses the unchanged shared composer and all twelve original control
   constructors. Actual native history preserves public bytes; state/memory
   matching derives row order, intermediate states and terminal PC/GPR reads.
   Scalar candidate queries also bound raw terminal PC limbs, including empty
   traces. Existing jump/branch fixtures and a reversed two-row JAL/JALR program
   pass; stale source data passes local constraints/decoding/state matching but
   fails memory matching. Keep the explicit initial CSR profile. This closes
   standalone checked control-family fetched composition, without adding a
   source closure premise. Continue with the remaining ordinary families below;
   new native program exports, whole-machine/protocol spans, general
   Rust/compiler and cryptographic refinement remain separate. No per-row
   result/PC or table-equivalence premise is added.

3. Port unsigned mul/div, shift/binop and subword memory into the same shared
   context; retain their family-specific assumptions and supported ISA profile.
   [Unsigned mul/div artifact import](Airbender/Review/Circuits/MulDiv/README.md)
   now retains all native equations and six paired-byte queries covering eleven
   8-bit columns. Actual table-driver rows and exact tagged Clean membership
   have symbolic certificates; native constraints derive every byte bound.
   Optimized-out scratch variables remain unconsumable. Importer mutation
   checks cover pairing/padding, scratch uses and native profile geometry.
   Native MUL/MULHU/DIVU/REMU numerical results now follow from every accepted
   equation/query, including zero divisors and actual masked x0 writes. The
   unchanged shared integer product theorem has its native v2 byte/carry
   connection; remainder comparison uses checked inverse 32768 and the native
   packed mask. Forty full local assignments apply the public numerical claim.
   Actual stateful original Sail decoding now derives packed operation and
   destination-zero metadata. Initialized native matching/public seeds derive
   every read/write/terminal bound and newest-read history; the short public
   trace claim obtains all four numerical results without local interfaces.
   Sixteen complete initialized traces and disabled-M/wrong-tag/bad-flag checks
   pass. The unchanged source decoder-frame proof retains actual misa reads.
   Actual Sail operand/old-destination reads, masked writes and every segment
   state now follow from initialized native history, including aliases and x0.
   Original three-port declarations are copied unchanged and bound to native
   v2 metadata. Actual native GPR histories preserve code/misa and replay the
   stateful original decoder after real updates. Sixteen cases and a reversed
   aliasing two-MUL program pass; stale old-destination metadata passes local
   constraints/decoding/state matching but fails native memory matching.
   Original MUL/MULHU/DIVU/REMU clauses and local nextPC preparation/PC
   retirement now follow from those constructed histories. Native PC gates
   derive bounded modular RV32 successors, including a full imported-row wrap
   regression. Sixteen initialized cases and actual second-MUL alias retirement
   pass. Complete fetched MUL/DIV execution now derives every original
   fetch/decode/preparation/retirement step, the actual native PC chain and
   terminal register reads. Stateful composition reuses the unchanged original
   misa-frame theorem and derives replay through actual native history/PC
   updates, without pure-decoder, extra ISA, row-step, intermediate-state or
   terminal-bound premises. Sixteen complete cases, concrete arithmetic final
   values, a newest-first two-MUL alias program reaching PC eight/x1=x3=861,
   and empty execution pass. Shift/binop now has an actual native decoder export
   and an independent public-byte/original-Sail certificate for all twelve
   ordinary forms, their original x0 variants, an unsupported ADD hole and all
   1,048,576 rows. Native v2 masks, full immediate limbs and SRAI encoded funct7
   differ from v3 and are checked directly. Empty CSR allow-list filtering and
   unsupported REV8/rotate/shift words are reproduced through the actual Rust
   API. Continue with native dynamic selectors/table import and exact membership,
   then numerical soundness, initialized execution and subword memory. Keep
   custom CSR/oracle semantics separate; dynamic compiled lookups still reject. The
   actual native zero/XOR/OR/AND low-ID prefix is now reproduced, with checked
   compiled offsets, all 196,608 binary outputs, actual zero row and exact
   original Clean/native membership. Native membership derives byte bounds and
   bitwise results; malformed keys/results reject. Geometry is structural and
   all output calculations reuse the source literal-block certificates within
   unchanged memory caps. Native truncation, zero-padded range and all 2,097,152 sign-fill rows now have checked
   actual-data/Clean membership, derived key/limb bounds and exact RV32 masks.
   Symbolic 64-domain block proofs retain native shift-zero behavior and original
   compiled noncontiguous offsets. Negative/positive sign boundaries and malformed
   queries pass. The actual low-input SRL table now has complete original
   Clean/native membership and exact zero-extended RV32 logical-shift semantics
   for all 2,097,152 rows, with derived key/output bounds and zero high output.
   Six symbolic certificates retain all 74 native blocks and compiled offset
   4460545 without row enumeration. Shift/final-bit boundaries and malformed
   queries pass. The actual high-input SLL table now also has complete original
   Clean/native membership and exact wrapped RV32 semantics for all 2,097,152
   rows, with derived bounds and zero low output. Six symbolic partitions and
   ten stored-template certificates retain all 74 native blocks, original
   offset 2363393 and actual shift/discard boundaries. Generic size/output
   assembly keeps imported arrays out of metadata normalization, under the same
   caps. Low-input SLL now also has exact actual-data/Clean membership and
   reconstructed RV32 results for all 2,097,152 rows, deriving both limb bounds.
   Its low column is identified with checked native SLL-high; all 145 high-output
   blocks retain native carry/truncation, with six symbolic prefix certificates
   and a 73-block suffix transported from that existing proof. First-carry,
   shift-sixteen and final-bit/discard boundaries pass under unchanged caps.
   High-input SRL now also has exact actual-data/Clean membership and RV32
   results for all 2,097,152 rows. The full high column reuses checked SRL-low;
   all 146 low-output blocks retain rotated/cross-shift templates, the 65,537-row
   initial zero block and the shortened shift-eleven affine block. Ten bounded
   template certificates, five symbolic partitions and a transported 73-block
   native SRL-low suffix derive every value and both limb bounds. All four native
   logical-shift limb tables now have checked helper membership/results.
   The complete shift/binop local projection now retains all fifty equations,
   eight timestamp queries and four dynamic table selectors as fourth Clean
   lookup fields. Twelve structural region proofs retain all 10,817,537 tagged
   rows with original offsets, including the exact compilation fixture CSR
   profile (nondeterminism enabled, empty delegation CSR list). Explicit-target, arity,
   mapping, placement and crossed-profile regressions pass. Runtime CSR setup
   binding remains separate; no custom CSR execution claim is inferred.
   All four actual tagged queries and their exact canonical selector domains now
   follow from native constraint acceptance. An exhaustive partition of every
   stored region proves unique tags and resolves native membership to the checked
   helper results; the actual zero row permits only three zero fields. Combined
   table regressions reject incorrect results/selectors and crossed SLL regions.
   Original public construction and native decoder membership now derive the
   six operation/immediate bits, all four native lookup tags, selected operand
   limbs and disabled ordinary delegation multiplicity. The six-bit bound rejects
   the complete sentinel tail. Full native fixtures cover all twelve forms and
   their x0 variants; all 96 tagged queries and public routing applications pass.
   Native XOR/OR/AND now derive all four accepted byte queries, both source-word
   bounds and exact selected RV32 results, including immediate forms. Native
   inverse-256 equations reconstruct all input/output limbs; original decoded x0
   flags derive the actual masked writes. Twelve complete binary fixtures retain
   sign-extended immediates and word values above Mersenne31; corrupted bytes,
   selected results and x0 writes reject under unchanged caps.
   Continue with native shift selected/written word results, then native
   clocks/ports, initialized history and original Sail execution.
   Derive actual source reads and states from native matching/public history.
4. Rebind bigint/BLAKE/Keccak workers and callers. Retest control validity,
   unissued workers, ROM behavior and request participation on v2 before reusing
   any source finding or temporary premise.
5. Port unified execution, protocol spans, terminal boundaries, padding and
   initialization/teardown under their actual v2 argument interfaces.

Expand importer support only when a concrete circuit requires it. The two native
word-memory and two native control fixed tables are now supported with exact
three-column queries and explicit profiles. The unsigned mul/div paired-byte profile is also supported with exact tagged
native data and checked odd-column zero padding. The exact four-witness shift/binop
profile now has complete tagged import. Other fixed tables, unsupported dynamic
selector profiles, unpaired byte columns and state linkage continue to fail closed.
Do not copy unused v3 Review theorems into the v2 build.

## Deferred milestones

Faithful Rust/JSON/Lean generation, full compiled argument correspondence,
cryptographic lookup/memory/statement enforcement and completeness remain
separate milestones. Every promoted public theorem needs a nonvacuous regression,
an explicit axiom root and resolved review-guide links.
