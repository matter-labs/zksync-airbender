# Circuit formal verification plan

Backport the current formalization to Airbender v2 on dev while preserving its
small review surface, directory roles, pinned references and explicit trust
boundaries. This document is a snapshot of pending work; checked coverage lives
in [Verification status](VERIFICATION_STATUS.md), and accepted counterexamples
and unresolved connections live in [Findings](FINDINGS.md).

## User priority: native reduced machine (2026-10-21)

Work directly on the [regenerated combined reduced circuit](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
and its original Sail execution connection now. The six standalone-family
checkpoints are reusable components; they do not establish reduced-machine
coverage. Do not complete remaining standalone/subword work first. The
[native reduced path](../../cs/src/machine/ops/unrolled/reduced_machine_ops.rs)
uses LoadOp with SUPPORT_LESS_THAN_WORD=false and StoreOp with the same flag
false. Subword retirement is therefore not a prerequisite for this machine.
This explicit user priority supersedes the older ordinary-family-first order
in the historical checkpoints below.

**The reduced machine has no execution soundness theorem yet.** The active
[regenerated native target](Airbender/Review/Circuits/ReducedMachine/NativeArtifact.lean)
is independently reproducible from unchanged pinned Rust: 117 equations,
142 variables and 14 fixed regions. The original [historical artifact](Airbender/Review/Circuits/ReducedMachine/Artifact.lean)
retains 119 equations, 141 variables and 13 regions; no equivalence is assumed.
The complete current native fixed pool and explicit public fixture are imported,
and original Clean acceptance now derives both actual sign/high-byte queries.
Full combined row effects and execution remain pending. See the
[current adaptation snapshot](V3_ADAPTATION.md). Stage-two JSON remains opaque.

1. Generalize the actual native pool beyond its explicit public image/CSR fixture,
   prove the remaining regions' operation semantics and connect physical setup.
   All 14 literal regions, exact tags and sign/high-byte recovery are checked.
   Do not inherit standalone fixture configuration, supplied row answers or v3 encodings.
2. Derive operation-specific native selector identities and flags, operand routing,
   actual masked writes, PC/clock effects and original Sail clauses. The domains
   of all four dynamic table selectors and both sign/high-byte queries are now
   derived from the regenerated constraints and complete pool. Shift masks now
   recover the operation flags, all four selected tags, actual register/immediate
   source-two routing and exact five-bit truncation. The explicit decoded mask
   now follows for the selected original shift profile from stateful public Sail
   decoding and complete sparse/padded membership at the actual native query.
   Native equations exclude holes/tail; source/rd/x0/immediate fields are recovered.
   Native preprocessing/fixed-ROM fidelity and other profiles remain separate.
   Actual sign-fill outputs
   are now derived, including minor flags and positive/logical/zero-shift cases.
   Both actual table-37 queries, contribution assembly, destination address, masked
   port write and default-PC candidate selection are now derived from native
   equations. All 4,194,304 actual table-37 rows now have checked numerical
   meanings, including the merged boundary and reversed right outputs. Complete
   native-pool membership derives canonical keys, exact arithmetic outputs and
   bounds; the selected native row derives all four contribution values/bounds
   at its actual field-packed keys. Initialized selected-shift traces now derive
   every read/write/terminal word bound and both canonical source keys from public
   seeds, original public decoding and actual fixed-pool native acceptance. Internal
   natural candidate values/bounds and masked-write preservation are proved for
   all 32 amounts, including x0 and arithmetic zero shift. Complete canonical RV32
   candidate/write results now follow from those initialized ranges, actual native
   equations and original decoded rd/x0. Original Sail cell/GPR transport and
   instruction execution, other profiles and numerical PC successor remain open.
   The former projection allocation gap is closed by generic projections and separate proof units,
   without increasing limits or adding result/equivalence premises.
3. Compose initialized combined histories, public decoding and original execution.
   Actual regenerated reduced timestamp equations and all eight timestamp queries
   now discharge the unchanged shared clock contract. Public seed construction
   plus accepted native state/memory matching derive full logical memory history,
   newest preceding reads, all local/prior clock bounds and terminal four-tick
   row accounting. Proved selected-shift write preservation now feeds shared
   range induction and derives the formerly unchecked low source limb, all other
   native word ranges and both canonical source keys. Concrete fixedData selects
   the actual certified native pool without an equivalence premise. Extend proved
   local preservation/public decoding to other combined operations. Selected-shift
   canonical RV32 words now follow, while original cell/GPR and full instruction
   execution remain unfinished.
4. Connect native delegation workers/callers and supported public use.
5. Close combined protocol, terminal/padding and initialization/teardown boundaries.

The new v3 reference is PR #585 at b29277dd895499574e317a994fd89243a72f06cb.
Its unified and reduced unrolled targets are distinct; the monolithic v2 reduced
artifact maps to the unified migration path. Its newer compiler certificates and
initialization contracts are dependencies to adapt, not established v2 coverage.
Preserve original Clean/Sail semantics and existing resource caps. Do not replace
missing obligations with desired outputs, table equivalence or intermediate states.

## Unchanged-circuit policy (6 November 2026)

Continue to checked parity with the current v3 formalization without fixing
production circuit or machine code. A confirmed native v2 issue must retain its
pinned evidence and exact acceptance scope in the findings register, and any
required restriction must appear as a narrow, explicit Review interface
assumption. Such an assumption is a conditional theorem boundary, not a fix or
an enforcement proof; it must not be implemented as a project axiom or a
premise that supplies the desired result. Coverage gaps and importer limitations
remain open obligations, not findings. No native v2 defect is currently established.

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

The user authorized continuation and regular commits on 17 October, stopped the
scheduled task on 21 October, and resumed foreground work on 6 November against
the latest PR #585. A continuation task, Continue v2 FV to v3 parity,
is active every 30 minutes at the user's request; the old task remains paused. Keep working
in the isolated dev-based worktree and make small verified unsigned Conventional
Commits, with Git signing disabled per invocation rather than configuration.
Do not push without authorization. Use the
[serial bounded verification runner](scripts/check_all.py) and its
[validated watchdog](scripts/bounded_fv.py): one Lean worker, Lean memory cap
3072 MiB, total footprint at most 3072 MiB, resident at most 4096 MiB and finite
wall budgets. Confirm termination after limits and redesign instead of raising caps.
This sampled guard and Lean allocation cap are not an OS hard physical-memory limit.

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
   Native SLL/SRL/SRA contributions now follow from original public decoding,
   all four accepted queries and native equations. The low operand is bounded
   and truncated modulo 32; each canonical packed key has exact bounded native
   contribution semantics. Both actual selected-limb sums and RV32 contribution
   addition are derived without input-range or desired-output premises. Twelve
   complete shift fixtures retain SRAI encoded funct7, native sign-fill order,
   shift-31/x0 boundaries and malformed key/inactive/sign-fill rejection.
   Native clocks/ports and complete initialized Clean history now follow from
   actual public Sail seeds/PC and accepted native matching. All twenty-four
   ordinary/x0 fixtures retain actual masked writes and readonly refreshes;
   six immediate/x0 stale-clock alternatives pass local equations but fail full
   memory matching. Native two-carry equations and eight timestamp queries derive
   all row/prior bounds, alignment and port order without local clock premises.
   Initialized word bounds and canonical packed-key source binding are now
   derived from actual public code, Sail seeds/PC and accepted native matching.
   Separate bounded SLL/SRL/SRA half calculations cover all shift amounts/signs;
   shared time induction supplies read bounds, exact masking bounds actual writes
   and natural key lifting recovers source/amount quotient and remainder.
   All twenty-four ordinary/x0 fixtures and twelve concrete shifts pass these
   public claims without local range, source/key or desired-output premises.
   Whole ordinary SLL/SRL/SRA/XOR/OR/AND numerical results and canonical actual
   selected/write limbs now follow from public decoding and initialized native
   history, with no local source/range or desired-result premise. Separate whole
   SLL/SRL/SRA calculations cover all 32 amounts and both sign domains; low-limb
   truncation equals the whole selected operand's architectural low-five bits.
   All twenty-four ordinary/x0 traces apply the short public numerical claim and
   derive concrete results. SRA sign calculations remain split under default
   heartbeat and fixed memory caps. Actual original Sail cell/GPR transport is
   now constructed from initialized matching and original public decoding: all
   native-clock-ordered segment states, common pre-state source/old-destination
   reads, actual masked writes, final cell matching and code/misa preservation
   are conclusions. The three original pinned register-port transport declarations
   are reused unchanged with checked v2 metadata; stateful original decoding
   replays after actual GPR updates. Twenty-four complete fixtures derive actual
   transfers/numerical writes; all twelve x0 variants preserve the entire Sail
   data state, including the six immediate/x0 readonly aliases. Original clauses are now
   checked for all six ordinary operations and twelve register/immediate forms:
   actual native routing/public immediate columns derive the selected operand,
   SRAI's encoded funct7 bits provably leave its low-five-bit shift count unchanged,
   and native numerical results/masked writes execute the retained original Sail
   instruction into the same actual history after-state. The short public
   clause-history claim derives source bounds and all row states from initialized
   native matching and original public decoding. Twenty-four complete fixtures
   reach actual original clause execution; all twelve x0 variants preserve the
   whole data state. The RV32 profile continues to reject amounts 32 and 63.
   Original preparation/retirement and complete fetched execution are now checked
   for this selected ordinary profile. Actual native carry gates derive outgoing
   PC bounds and modular +4; public original setup derives incoming PC bounds and
   alignment. Complete native rows check low carry and full RV32 wrap. Actual GPR
   history supplies every state/read and preserves code/misa, so original stateful
   decoding replays in each real pre-state. Native PC matching composes finite
   original fetched steps to exact terminal PC/cells, including empty traces.
   Twenty-four complete fixtures derive original retirement, actual terminal PCs
   and GPR values; all twelve x0 forms advance PC while preserving data. Continue
   with remaining ordinary/subword-memory coverage and runtime CSR setup binding
   before delegation workers/callers and unified protocol boundaries below.
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

## Findings discipline

Use the [same finding-status bar as the pinned v3 review](FINDINGS.md#assessment-standard):
retain accepted native/reference discrepancies and concrete source defects at their
exact scope without requiring a full forged proof. An assumption or narrower
conditional theorem is not a fix. Keep unresolved bindings and supported profiles
explicit, retest v3 candidates on actual v2 paths, and put coverage/milestone notes
in verification status rather than inflating the findings register.

## Native subword offset/trap table checkpoint (2026-10-20)

The native v2 offset/trap table now has an actual export and a complete kernel
certificate for all 2,097,152 rows. Its native tag is 44 and its compiled offset
is 65,537. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordOffsetData.lean)
comes from the unchanged pinned table generator and lossless shared codec;
[strict import](Airbender/Import/Setup.lean) rejects changed field, profile, tag,
placement, extent, shape and noncanonical values. The standard native gate
reproduces the JSON byte for byte under the existing shared-lock watchdog.

[The small public helper](Airbender/Review/Helpers/Tables/SubwordOffsetTheorems.lean)
derives a canonical 21-bit key, its exact low-two-bit offset and the complete
native width/limb/trap mask. [Internal calculations](Airbender/Proofs/SubwordMemory/Offset.lean)
check all stored blocks symbolically over 32 control groups and every low-address
pattern, and prove exact original Clean/native tagged membership without a table
equivalence premise. The original affine getter and membership transport are
reused from verified v2 certificates. No proof or resource ceilings were raised.

[Regressions](Tests/SubwordOffset.lean) retain ordinary misaligned halfword/word
loads, the explicit native misaligned-load-to-x0 exception, high-half selection,
invalid encoding and store controls, and reject altered offset/trap queries.
The table alone admits some keys that the full decoder/circuit must assess.
No accepted subword row, Sail execution or native defect is claimed here. The
remaining load/store/ROM regions, full native constraint import, public decoding,
initialized reads and original subword instruction execution remain unfinished.
The findings standard and historical findings/coverage archive are unchanged.

## Native subword load-data table checkpoint (2026-10-20)

The native v2 signed/unsigned load-data table now has a complete certificate for
all 2,097,152 actual exported rows, with native tag 45 and compiled offset
2,162,689. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordLoadData.lean)
comes from the unchanged pinned native generator and shared lossless codec.
The strict importer checks field, profile, tag, placement, extent, shape and
canonicality; the standard native gate reproduces the JSON byte for byte.

[The public helper](Airbender/Review/Helpers/Tables/SubwordLoadTheorems.lean)
derives the canonical 21-bit key, exact signed/unsigned low and high outputs,
and both 16-bit bounds directly from original Clean lookup membership. The key
retains its preselected 16-bit limb, two offset bits and funct3. Odd-halfword and
unused/invalid keys retain the native zero outputs; their isolated presence is
not an accepted-row or architectural defect claim.

[Internal assembly](Airbender/Proofs/SubwordMemory/Load.lean) proves exact tagged
native/Clean membership. Symbolic getters and 32 control groups cover every
stored affine/periodic block. The pinned v3 block-selection lemmas are copied
unchanged. Four actual 256-entry templates use 64 separate 16-entry kernel
certificates, each in a fresh bounded worker. Literal constants share data without
changing values or codec semantics. This replaces an allocation-heavy draft;
no memory, recursion or heartbeat limits were raised.

[Nineteen kernel regression roots](Tests/SubwordLoad.lean) cover byte sign
boundaries, signed halfword boundaries, all four offsets, unsigned outputs,
odd-halfword and unused keys, and rejection of altered low/high values. Fourteen
additional importer checks reject malformed native load-data artifacts.
Full subword constraints, remaining store/ROM regions, public decoding,
initialized native memory/history, original instruction execution and physical
argument binding remain unfinished. The findings standard and historical
findings/coverage archive are unchanged.

## Native subword original-RAM clearing table checkpoint (2026-10-20)

The native v2 original-RAM-limb clearing table now has a complete certificate for
all 2,097,152 actual exported rows. Its native ID is 54 and compiled offset is
5,308,417, obtained from the actual generator and compiled layout. [Literal data](Airbender/Review/Helpers/Tables/NativeSubwordStoreClearData.lean)
uses the unchanged pinned native generator and lossless shared codec. Strict
import checks field, profile, tag, placement, extent, shape and canonicality;
the standard native gate reproduces the JSON byte for byte.

[The short public helper](Airbender/Review/Helpers/Tables/SubwordStoreClearTheorems.lean)
derives the canonical key, exact retained original RAM byte, unused zero output
and 16-bit bound from original Clean lookup membership. The key retains the
preselected limb, both offset bits and raw funct3. SB preserves the byte outside
the selected write position. SH, SW and all unused funct3 keys retain the native
zero outputs. These isolated keys do not establish accepted full store behavior.

[Internal proof assembly](Airbender/Proofs/SubwordMemory/StoreClear.lean) covers
all actual affine/periodic blocks symbolically over 32 control groups, reusing
the verified native block helpers and pinned v3 periodic upper-byte proof.
Exact tagged native/Clean membership is proved; no table-equivalence premise,
expected output, new axiom or increased proof/resource limit is used.
[Fourteen kernel regression roots](Tests/SubwordStoreClear.lean) cover all four
offsets, retained/cleared byte boundaries, SH/SW/unused zero outputs and rejection
of changed clearing or unused fields. Fourteen new importer checks retain strict
malformed-artifact rejection and crossed native-region checks.

The written-value placement table, subword ROM regions, full native constraints,
limb preselection, public decoding, initialized memory/history, original subword
instruction execution and physical argument binding remain unfinished. No native
defect is established; the findings bar and historical coverage archive are unchanged.

## Native subword written-value placement checkpoint (2026-10-20)

The native v2 written-value placement table now has a complete certificate for
all 2,097,152 actual exported rows, native ID 55 and compiled offset 7,405,569.
[Literal data](Airbender/Review/Helpers/Tables/NativeSubwordStorePlaceData.lean)
comes from the unchanged pinned generator and shared lossless codec. Strict
import retains exact field, profile, tag, placement, extent, shape and canonical
values; the standard native gate reproduces the JSON byte for byte.

[The public helper](Airbender/Review/Helpers/Tables/SubwordStorePlaceTheorems.lean)
derives canonical key, exact SB/SH contribution, unused zero and 16-bit output
bound from original Clean lookup membership. SB selects the source low byte and
places it by offset parity; SH retains the whole preselected limb at every raw
offset. SW and unused funct3 keys retain zero outputs. The presence of odd SH
keys in this isolated table does not establish full circuit acceptance.

[Internal assembly](Airbender/Proofs/SubwordMemory/StorePlace.lean) checks all
native affine/periodic blocks across 32 control groups, adapting the pinned v3
placement proof and reusing the verified v2 block helpers. The nondependent
periodic getter is copied unchanged. Affine literal arrays compare every parsed
element against the actual first/step/length before compact emission; prior
emitter modes remain unchanged. Sample and size lemmas are structural. General
Rust/JSON/elaborator fidelity remains the separate Import boundary; no theorem
assumes table equivalence, expected results or new axioms, and no limits are raised.

[Fifteen kernel regression roots](Tests/SubwordStorePlace.lean) cover all offsets,
source high-byte removal, SH full/odd raw keys, SW/unused zeros and changed-query
rejection. Fourteen new importer checks retain malformed-artifact rejection and
crossed native-region tests. Remaining subword ROM regions, full native constraints,
limb preselection, public decoding, initialized memory/history, original instruction
execution and physical argument binding remain unfinished. No native defect is
established; the findings standard and historical coverage archive are unchanged.

## Complete native subword lookup import checkpoint (2026-10-20)

[The artifact](Airbender/Review/Circuits/SubwordMemory/Artifact.lean) retains all
51 native equations, two scalar queries, eight timestamp queries, two constant
fixed queries and both multiplexed witness-selected queries. [Structural checks](Airbender/Proofs/SubwordMemory/ArtifactChecks.lean)
retain actual state/decoder columns, all three memory ports and clocks, and
complete setup geometry. The importer requires the exact selector profile, all
62 table offsets and the 9,502,721-row tagged extent. Prior validation remains;
the CLI gate now covers all six native compiled layouts.

[The complete table](Airbender/Review/Circuits/SubwordMemory/Tables/Native.lean)
keeps all seven native regions: zero, separator, offset/trap, load-data, aligned
word ROM, original-RAM clearing and written-value placement. Previously checked
literal fixed data is unchanged. [Internal structural proofs](Airbender/Proofs/SubwordMemory/NativeLookup.lean)
include every row in each region. [The short public claim](Airbender/Review/Circuits/SubwordMemory/Lookups.lean)
derives both actual queries and evaluated selectors from original Clean native
acceptance, with no expected result, selector bound, intermediate state or
table-equivalence premise.

Earlier references to remaining subword ROM regions were a planning expectation.
Actual v2 has one AlignedRomRead region, tag 46, keyed by aligned word index;
v3's separate byte/halfword ROM regions do not apply. [The aligned model](Airbender/Review/Helpers/Tables/AlignedWordROM.lean)
shares the full public WordROM image and native UNIMP tail. Ordinary RomRead has
a byte-address key and tag 24. [Symbolic proofs](Airbender/Proofs/Tables/AlignedWordROM.lean)
derive the canonical index and both limbs and connect the two row models' word
values. General Rust/JSON/compiler/setup correspondence and physical verifier
enforcement remain separate boundaries; this adds no general native ROM-export
refinement claim.

[Thirteen kernel regressions](Tests/SubwordArtifact.lean) cover evaluated
selectors, native placements, distinct ROM key units, the complete UNIMP tail
and altered key/output rejection. Explicit macro guards reject missing/crossed/
duplicate profiles. Thirty-one new importer checks cover selectors/mappings,
tuple widths, all region offsets, extents and overlapping decoder placement.

Next are subword tag resolution, operation routing, actual limb preselection,
numerical load/store effects, public/native decoding, initialized memory/history,
original Sail execution and whole-machine composition. No native defect is
established. FINDINGS and its historical archive, original Clean/Sail semantics,
native source/exporter/codec and resource ceilings are unchanged.

## Native subword tagged-query resolution checkpoint (2026-10-20)

[Internal partition](Airbender/Proofs/SubwordMemory/NativeRegions.lean) now proves
the exact seven-region decomposition of the complete native subword table.
Literal fourth-column reads and public separator/ROM tags derive tag uniqueness
and the canonical selector set 0, 23, 44, 45, 46, 54, 55. No region is omitted
because it is expected to be unused by a later routing proof. The existing
affine tag getter is copied unchanged from the checked v2 shift-region proof.

[Exact resolution](Airbender/Proofs/SubwordMemory/NativeResolution.lean) connects
each selected tag to the already certified helper membership: offset/trap,
signed/unsigned load data, original-RAM clearing and written-value placement,
alongside the public separator and aligned word ROM. Tag zero requires the
actual all-zero query. These are proved equivalences, not assumed table-equivalence
premises. All native literal data, region offsets, import semantics and the
public ROM model are unchanged.

[The short public claims](Airbender/Review/Circuits/SubwordMemory/Lookups.lean)
expose these seven connections and canonical selector bounds. Both per-slot
bounds follow from original Clean native acceptance through the existing
accepted-query extraction theorem, which is retained unchanged. They require
no witness-supplied selector bound, expected result, routing or intermediate
state. Operation-specific tag choices still require the native routing equations.

[Thirty kernel regression roots](Tests/SubwordLookups.lean) cover every region,
separator boundaries, native trap and x0 raw keys, signed/unsigned loads, both
store byte positions, altered outputs/unused fields, crossed store regions,
unsupported tags, ROM word/byte key distinction, UNIMP tail and canonical field
tag wrap. Previous helper rejection proofs are reused. These malformed-input
rejections and isolated raw keys add no confirmed native defect.

Next: derive the ROM/RAM/load/store routing and actual limb preselection, then
numerical operation effects, public/native decoding, initialized memory/history,
original Sail execution and whole-machine composition. General native export/
compiler refinement, runtime CSR binding and physical verifier enforcement
remain separate boundaries. FINDINGS and its historical archive, native sources,
original Clean/Sail, exporter/codec and all resource ceilings remain unchanged.

## Native subword operation-routing checkpoint (2026-10-20)

[Controls](Airbender/Proofs/SubwordMemory/Controls.lean) derive store, size and
upper-limb Booleanity from native equations. The actual fixed separator derives
RAM/ROM selection and the low six high-address bits. Native acceptance excludes
stores into ROM. The two optimized equations determine tags 46/45 for ROM loads,
45/0 for RAM loads and 54/55 for stores. Native mixed-port modes/addresses and
three separate ROM/load-RAM/old-store-RAM limb muxes are also derived.

[Field selection](Airbender/Proofs/SubwordMemory/QueryFields.lean) derives all
three fields of both native dynamic queries in each accepted mode. V2 ROM keeps
its field inverse of four and word-index key. Load/clear/place keys retain the
actual offset and raw funct3 encoding. The inverse-coefficient proof pattern is
adapted from checked v2 binary-query proofs with small kernel-checked Mersenne31
characteristic identities; resource/proof limits and native coefficients are
unchanged. Selected limbs, query keys and results are conclusions, not premises.

[Four short public claims](Airbender/Review/Circuits/SubwordMemory/Routing.lean)
expose exhaustive accepted modes and the exact ROM-load, RAM-load and store
connections. [Observables](Airbender/Review/Circuits/SubwordMemory/RoutingModel.lean)
name selected native limbs and keys. [Internal assembly](Airbender/Proofs/SubwordMemory/Routing.lean)
uses original Clean acceptance and the existing proved tagged-table resolution.
A RAM load has an actual all-zero second slot. Stores query old RAM data for
clearing and the source register's low limb for placement. No result, table
equivalence, selector-bound or intermediate-state premise is added.

[Six complete native fixtures](Tests/SubwordRouting.lean) satisfy all 51 original
equations and fourteen lookups, with two-row proof partitions. They cover lower
and upper ROM loads, a nonzero ROM word index, signed odd-byte/upper-half RAM
loads, x0, an odd-byte store and a halfword store. Public routing claims are
applied to these accepted rows. Concrete writes and eight mutations check crossed
store tags, byte-address ROM keys, wrong RAM/store limbs, nonzero disabled fields,
ROM stores, non-Boolean upper selectors and mixed addresses. These local fixtures
do not assert public decoding, initialized history or original instruction execution.

Next: derive general numerical subword effects, decoder/control connections,
initialized reads and history, original Sail execution and whole-machine composition.
Five other ordinary families already have initialized fetched execution; the sixth
subword family, delegation/custom/CSR and unified/terminal/padding/initialization
boundaries remain unfinished. General export/compiler refinement and physical
verifier/cryptographic enforcement remain separate. No new confirmed native defect
is established. FINDINGS and its historical archive, native sources/artifacts,
original Clean/Sail, exporter/codec and all resource ceilings remain unchanged.

## Native subword value/write checkpoint (2026-10-20)

[Offset controls](Airbender/Proofs/SubwordMemory/OffsetValues.lean) now derive the
actual fixed offset query, its canonical key bound and exact offset/mask values.
Native Boolean size/upper controls and the packed-mask equation force the retained
mask below four, so a native trap bit cannot occur in an accepted row. The size
bit is the mask's low bit and the upper-limb selector is exactly offset / 2.
The original table, all trap rows and explicit misaligned-load-to-x0 exception
remain unchanged; this is native control reasoning, not an architectural alignment
or x0 correctness claim. A generic original Clean lookup bridge and three separate
field reductions avoid a recursion-limit failure without raising proof limits.

[Actual writes](Airbender/Proofs/SubwordMemory/WriteValues.lean) now connect native
ROM/RAM data outputs to both load-candidate columns and the actual written register
columns. The original (1 - rd_is_x0) scaling remains exact. For either supported
flag value, writes equal the candidate or zero; Boolean decoding itself is still
a public-decoder dependency, not a new local premise. Native store equations
assemble certified clearing/placement outputs, preserve the opposite old limb
in subword mode and retain the full-word source mux in the raw native relation.

[Value assembly](Airbender/Proofs/SubwordMemory/Values.lean) derives actual canonical
load candidate values and both candidate bounds, public word-indexed ROM contents,
cleared/placed values, their bounds and unused zeros. The v3 data/merge proof
approaches are adapted with exact source identities, alongside checked v2 reuse.
No v3 native result is assumed: actual v2 tables, field, query keys, columns and
write equations supply the connections. No expected result, selected read, table
equivalence, alignment or read bound is supplied as a premise.

[Five short public claims](Airbender/Review/Circuits/SubwordMemory/Values.lean)
use the small [observable interface](Airbender/Review/Circuits/SubwordMemory/ValuesModel.lean).
[Test applications](Tests/SubwordValues.lean) reuse all six complete native fixtures
unchanged, preserving signed data, upper/lower loads, nonzero ROM word indexing,
x0 and stores. The original nonzero x0 candidate is retained before its zero
write. Nine rejections cover changed ROM/RAM candidates, actual writes, nonzero
x0 writes, wrong offsets/upper selectors and a native trap-bearing key. Rejected
mutations are coverage evidence and add no confirmed native defect.

Next: connect actual native/public decoding to supported byte/halfword operations,
normalize packed raw keys over that domain, derive source/old-RAM read and whole
write bounds from initialized history, then reach original Sail execution and
whole-machine composition. Canonical lookup values and field write assembly do
not claim these remaining connections. The sixth ordinary family, delegation/
custom/CSR and unified/terminal/padding/initialization boundaries remain unfinished.
General export/compiler refinement and physical verifier/cryptographic enforcement
remain separate. FINDINGS and its historical archive, native sources/artifacts,
original Clean/Sail, exporter/codec and resource/proof ceilings are unchanged.

## Public subword decoding checkpoint (2026-10-20)

[Original public decoding](Airbender/Review/Circuits/SubwordMemory/Decoder.lean)
now projects all six supported original Sail forms: LB, LH, LBU, LHU, SB and SH.
The actual v2 decoder source is pinned. Its one-bit store mask and raw funct3
are retained, unused load rs2 and store rd clear, and original x0 loads remain
present. Signed immediate limbs are preserved. The v3 projection/proof approach
is adapted with exact provenance; its three-bit masks, x0 exclusions and native
connections are not copied into v2 coverage.

[Internal recovery](Airbender/Proofs/SubwordMemory/Decoder.lean) uses actual
public sparse-image construction, complete logical setup membership and original
native acceptance. Native store Booleanity excludes every unsupported slot and
the complete sentinel tail. The selected original public instruction supplies
all ten native query fields: PC, register indices, x0 flag, immediate, raw funct3
and store mask. No selector meaning or Boolean x0 flag is supplied separately.
Certified native candidate bounds plus the derived x0 flag give actual decoded
load writes and both written-limb bounds, including discarded x0 writes.

[Two short public claims](Airbender/Review/Circuits/SubwordMemory/Decoding.lean)
expose these connections without supplying expected reads/results or a table
equivalence. Calculations and proof assembly remain internal. This is logical
public-image membership; correspondence to an actual native exported subword
decoder table remains an explicit Import fidelity boundary. The source pin is
not an exported-table certificate or general Rust/compiler refinement claim.

[Seven complete native rows](Tests/SubwordDecoderFixture.lean) cover all six
forms, lower/upper ROM and RAM cases, signed/unsigned data, original x0 loads
and SB/SH. Existing six local fixtures remain unchanged. New rows clear their
unused load index and correct store rd/x0 metadata; an added LBU case has its
own native key, unsigned candidate and actual write. All 357 original equations
and 98 lookup memberships pass. Independent original instruction bytes construct
public one-word images with the full 1,048,576-row capacity; original decoding is
checked separately as small pure reductions. [Applications](Tests/SubwordDecoder.lean)
exercise both claims nonvacuously, signed immediate extremes, unsupported word
forms and five decoder-membership rejections. Old local rows remain accepted
locally and their incompatible decoder metadata is correctly rejected.

Concrete membership expansion initially reached Lean's allocation cap. Reusing
the existing symbolic sparse-head membership lemma avoids that expansion; query
metadata is reduced explicitly and original decoding is split from state replay.
No allocation, footprint, resident, recursion or proof ceiling is increased.
Every failed owned worker is confirmed terminated before retrying.

Next: certify actual native decoder exports, normalize packed subword keys over
the decoded domain and derive source/old-RAM reads and whole store-write bounds
from initialized history. Original subword Sail execution and composition remain
unfinished. The sixth ordinary family, delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain open. General
Rust/compiler refinement and physical verifier/cryptographic enforcement remain
separate. No confirmed native defect is added; FINDINGS and its historical
archive, original Clean/Sail, native circuit/helper artifacts and source checkout
are unchanged.

## Native subword decoder export checkpoint (2026-10-21)

[The actual native export](artifacts/setup/subword-decoder-native.json) now
retains thirteen original words: all six subword forms, their negative-immediate
variants with original x0 load destinations, and an unsupported LW slot. The
exporter calls the pinned original native subword family and shared preprocessor/
flattening functions; its codec, dependencies and other profile behavior remain
unchanged. The independent strict [parser](Airbender/Import/Setup.lean) and
[literal emitter](Airbender/Import/SetupEmbed.lean) retain the exact subword family,
Mersenne31 field, text bounds and full ten-column 1,048,576-row extent.

[Independent public data](Airbender/Review/Circuits/SubwordMemory/NativeData.lean)
spells original instruction bytes and Sail constructors separately from exported
metadata. [Small pure original reductions](Airbender/Proofs/SubwordMemory/NativeDecode.lean)
retain signed immediates and original x0 forms before replay in the public state.
[Byte reads and internal certificates](Airbender/Proofs/SubwordMemory/NativeSetup.lean)
construct the exact public indexed setup and prove equality with every actual
exported row. Four small byte-read partitions and symbolic compressed-column tail
getters preserve all default proof/resource ceilings; no million-row expansion,
expected result or table-equivalence premise is introduced.

[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/NativeDecoder.lean)
checks this specific export's fidelity. Native I-type unused rs2 is zero, original
x0 destinations retain zero flag one, and negative immediates use 65535/65535.
Native S-type raw bits contain apparent rd=31 for immediate -1; the actual decoder
clears that unused index, retains rs2 and sets zero flag one. The unsupported LW
keeps its physical slot and the entire sentinel tail is retained.

[Kernel regressions](Tests/SubwordNativeDecoder.lean) cover original text and
Sail decoding, full row equality, tail, signed x0 loads and negative stores.
Nineteen added importer checks reject bad/crossed profiles, altered fields,
noncanonical words, incomplete columns/extents and unknown fields. Native Rust
runs reproduce the fixture and independent little-endian text input; actual
word/doubleword/ADD/CSR filtering and malformed/oversized text rejection pass.
All previous native exports and importer checks remain covered.

This closes the specific decoder-data fidelity dependency, not arbitrary Rust/
JSON/compiler refinement or subword instruction execution. Native constraints,
initialized matching, public state/ROM bindings and packed-key normalization must
still derive source/old-RAM reads, whole store-write bounds and original subword
Sail execution. Five other ordinary families remain at their existing checked
execution checkpoints; delegation/custom/CSR, unified execution, initialization/
teardown and terminal/padding boundaries remain unfinished. Physical verifier
and cryptographic enforcement remain separate. No confirmed defect is added;
FINDINGS and its historical archive, original Clean/Sail and native sources/
circuit/helper artifacts are unchanged. The original checkout is preserved.

## Initialized native subword history checkpoint (2026-10-21)

The separate [native registry](Airbender/Review/Helpers/Context/SubwordMemory.lean)
retains the actual imported subword constraints, state, decoder and three mixed
register/RAM port descriptors. [Native clock extraction](Airbender/Proofs/SubwordMemory/Timestamp.lean)
checks the three Boolean comparison borrows, Boolean carry, both clock equations
and all eight timestamp queries against the subword artifact. These discharge
the unchanged [shared clock contract](Airbender/Proofs/Trace/Families/SubwordMemory/History.lean).
No v3 column identity or assumed table equivalence is used.

[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/History.lean)
now derives complete original Clean online memory history and every newest
preceding read from actual original Sail seed reads/PC and accepted native
state/memory matching. Row bounds, prior-clock bounds, alignment, port order,
history and read values are derived. Readonly ROM-shadow accesses and their
timestamp refreshes stay in matching, as do actual masked destination writes.

[Eight complete initialized traces](Tests/SubwordHistoryFixture.lean) cover
signed/unsigned byte and halfword loads, ROM shadows, RAM, x0 and actual SB/SH
writes. Their independent public registers and little-endian data bytes construct
the seed image. The eighth load aliases rs1=rd=1 and consumes the source port's
readonly refresh at clock four, using a unique seed domain. [The stale version](Tests/SubwordHistoryStale.lean)
still satisfies every local native constraint, but [logical matching rejects it](Tests/SubwordHistory.lean).
This is a regression for the intended matching boundary, not a confirmed defect.
Projecting to timestamp multiplicities makes rejection small without reducing
word/address payloads. Splitting local acceptance from history checks preserves
the existing Lean allocation/resource ceilings after an initial check hit the cap.

[Clock regressions](Tests/SubwordClock.lean) verify a full native row at low clock
524284: the actual carry advances to low/high 0/1 and clock value 524288, with all
three ports strictly after their prior clocks. Nonboolean carry and high-limb
overflow are rejected. All earlier decoder, table, routing, value and execution
checks remain unchanged. Calculations and assembly stay under Proofs; Import
keeps its separate data-fidelity boundary.

This closes initialized logical history for subword rows. Canonical source/old-RAM
word bounds, whole store-write bounds, packed byte/halfword key binding, public
instruction/data-ROM projection and original subword Sail execution remain next
dependencies. The fixtures do not yet identify their ROM-shadow data bytes with
architectural instruction bytes. Delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain unfinished.
General Rust/JSON/compiler refinement and physical verifier/cryptographic
enforcement remain separate. No confirmed defect is added; FINDINGS and its
historical archive are unchanged. Original Clean/Sail, native sources/artifacts,
exporter, earlier fixtures and the original checkout are preserved.

## Initialized native subword word bounds checkpoint (2026-10-21)

[Exact packed-key calculations](Airbender/Proofs/SubwordMemory/PackedKeys.lean)
now recover the native 16-bit limb, two-bit offset and three-bit raw funct3
without Mersenne31 wrap. Native offset/upper controls, canonical reads and
original public metadata supply the ranges. [Store preservation](Airbender/Proofs/SubwordMemory/StoreBounds.lean)
uses the already certified literal native clear/place relations and actual
write muxes. SB's complementary bytes bound their sum; SH replaces the selected
limb and unused raw rows contribute zero. The opposite old limb and native
full-word mux branch are retained. Separate contribution bounds alone are not
used to justify a bounded sum.

[The initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/Values.lean)
derives original raw funct3 and x0 masking from actual public decoding. Readonly
ports preserve their read words. The last store write uses both the earlier
source read and its old destination/RAM read. The unchanged shared time induction
then derives every native read, write and terminal payload range from actual
public Sail seeds and native matching. [One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Values.lean)
uses the same actual public state for initialization and full sparse decoder
construction. No per-row bound, clock, expected read, result, intermediate state
or table-equivalence premise is introduced.

[Eight complete initialized decoded traces](Tests/SubwordWordBounds.lean)
exercise all six forms, RAM/ROM-shadow loads, actual SB/SH writes, x0 and an
rs1=rd alias consuming the source refresh at clock four. Independent actual
instruction bytes and register/data bytes now share one public Sail state.
Three new row copies change only shadow read/selection columns when the shadow
overlaps instruction address zero; earlier fixtures remain unchanged. Every
native equation and lookup is checked. This joins decoding and logical memory
initialization; architectural data-ROM lookup contents remain a separate binding.

[Boundary regressions](Tests/SubwordPackedBounds.lean) retain the largest native
key, maximal byte merges, halfword/unused rows and the insufficiency of separate
contribution bounds. A Mersenne31 packed-field alias explains why raw funct3
ranges matter; the integrated claim derives those ranges from actual original
public decoding. These regressions do not establish a confirmed defect.

Draft combined fixture/closed-relation assembly checks hit Lean's allocation
cap and terminated with no surviving owned workers. Three native certificates
are now split, and one generic assignment-transport lemma precedes finite
specialization. The final checks preserve all default/resource ceilings; no
memory increase, semantic restriction, truncated table or expected-result
assumption was introduced. The disjoint-merge and two-read history arguments
adapt the pinned v3 source with accurate provenance; shared Clean/Sail/value
semantics and native v2 sources/artifacts/exporter are unchanged.

Next work binds bounded source/old-RAM words and native effective addresses,
size/sign/offset selectors and load/store packed fields to original Sail byte/
halfword effects, then prepares/retires and composes full subword execution.
Architectural instruction/data-ROM projection remains explicit. Delegation/
custom/CSR, unified execution, initialization/teardown and terminal/padding
boundaries remain unfinished. General Rust/JSON/compiler refinement and physical
verifier/cryptographic enforcement remain separate. FINDINGS and its historical
archive are unchanged; no confirmed defect is added. The original checkout is
preserved and no push/publication is authorized.

## Initialized native subword address checkpoint (2026-10-21)

[Native Mersenne31 addition](Airbender/Proofs/SubwordMemory/AddressArithmetic.lean)
now derives the effective RV32 byte address from the actual source and decoded
immediate limbs. The existing word-memory carry calculation is reused with the
checked native subword equation indices. Both scalar address queries supply
canonical limbs; low and high carries retain native RV32 wraparound.

[Offset and port geometry](Airbender/Proofs/SubwordMemory/Address.lean) derives
canonical native offset-key packing from the ranged address, original raw
funct3/x0 fields and native store Booleanity. Accepted fixed-table membership
then yields the byte offset. Native subtraction recovers the containing aligned
word without field wrap or natural underflow. Its address is exactly byte-address
floor division by four, including the top RV32 word, and adding the derived
offset recovers the byte address. The actual mixed load/store port address is
that containing word; no cell, address, alignment or expected-result premise is
supplied.

[Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/Address.lean)
uses the same original public Sail state for seed reads and full sparse decoding.
The established history supplies the actual first-port source range; original
decoding supplies the immediate and raw/x0 ranges. [One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Address.lean)
derives actual public source evidence, decoded metadata and every native address
property. No caller-supplied row read, bound, clock, flag or intermediate state is
added. The observables remain in Review and all arithmetic/assembly remains in
Proofs.

[Eight unchanged complete initialized traces](Tests/SubwordAddresses.lean) now
exercise address and port geometry for all six forms, actual SB/SH writes, x0,
ROM-shadow/RAM data and a source/destination alias. [Two split complete-native
boundary certificates](Tests/SubwordAddressBoundaries.lean) retain all 51 native
equations and 14 lookups each: 0xffffffff plus one wraps to zero with both native
carry levels, and zero plus original sign-extended minus three yields byte
address 0xfffffffd and containing word 0xfffffffc. Actual original instruction
decoding and native metadata/query fields are checked. The boundary certificates
are address regressions; they do not claim original instruction execution.

Next work binds width/sign/offset selectors and the bounded source/old-memory
words to original Sail byte/halfword load/store effects, then prepares/retires
and composes full subword execution. Architectural instruction/data-ROM
projection remains explicit. Delegation/custom/CSR, unified execution,
initialization/teardown and terminal/padding boundaries remain unfinished.
General Rust/JSON/compiler refinement and physical verifier/cryptographic
enforcement remain separate. FINDINGS and its historical archive are unchanged;
no confirmed native defect is added. Resource ceilings are unchanged, the
original checkout is preserved and no push/publication is authorized.

## Initialized native subword load-value checkpoint (2026-10-21)

[Two shared mathematical lemmas](Airbender/Proofs/SubwordMemory/ByteMath.lean)
copy the pinned v3 statements and proof bodies unchanged: bounded limb sign/
zero extension and byte/halfword extraction. [The v2 connection](Airbender/Proofs/SubwordMemory/LoadExtension.lean)
uses the actual raw-funct3/two-bit-offset keys and the already certified complete
literal native load tables. It retains odd-halfword zero rows and unused keys;
no native v3 field, inverse, key, table or selector identity is imported.

[Native data controls](Airbender/Proofs/SubwordMemory/DataControls.lean) recover
raw funct3, load and x0 key bits without Mersenne31 wrap. Original decoded fields
and actual fixed-offset membership derive the subword mux and upper selector.
Retained halfword loads and stores align through absence of the native trap bit.
Discarded loads retain the native waiver; unconditional alignment is not assumed.
[Exact ROM indexing](Airbender/Proofs/SubwordMemory/ROMAddress.lean) proves that
the native inverse-of-four query names the actual containing word index, then
recovers both complete ROM limbs, including native UNIMP padding. Architectural
instruction/data-ROM byte binding remains separate.

[Actual native load data](Airbender/Proofs/SubwordMemory/LoadData.lean) derives
both offset bits, the selected limb and the packed key from accepted controls
and actual bounded words. Native RAM/ROM candidates then equal the original
Sail extension of the selected byte/halfword slice. The actual x0 flag controls
the actual masked write. [Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/LoadData.lean)
and [one short public claim](Airbender/Review/Trace/Families/SubwordMemory/Loads.lean)
use one original public state for seed reads and full sparse decoding. Existing
history supplies actual read bounds; no row read/range, sign, size, alignment,
expected result, table equivalence or intermediate state is supplied.

[Eight unchanged complete initialized traces](Tests/SubwordLoadData.lean) retain
all six forms, actual stores, x0, aliases and distinct native ROM versus logical
instruction-shadow data. [Independent boundary checks](Tests/SubwordLoadExtension.lean)
exercise signedness thresholds, all byte positions and odd-halfword helper rows.
[A ninth complete initialized decoded trace](Tests/SubwordOddX0.lean) retains
odd LH-to-x0 with every native equation, lookup, state/memory match and actual
public byte/seed read. Its offset is three, both candidate limbs are zero and
the actual masked write is zero. This prevents treating unconditional halfword
alignment as a consequence of the accepted logical relation. Original Sail
access/exception/retirement comparison for this case remains unproved; neither
an original instruction success nor a defect or repair is claimed here.

Next work connects store byte-window effects, actual architectural read/write
history and ROM bytes, native subword PC/prepare/retire behavior and full original
instruction execution. Delegation/custom/CSR, unified execution, initialization/
teardown and terminal/padding boundaries remain unfinished. General Rust/JSON/
compiler refinement and physical verifier/cryptographic enforcement remain
separate. FINDINGS and its exact historical archive are unchanged; no confirmed
native defect is added. Resource ceilings are unchanged, the original checkout
is preserved and no push/publication is authorized.

## Initialized native subword store-byte checkpoint (2026-10-21)

[Pure byte arithmetic](Airbender/Proofs/SubwordMemory/StoreBytes.lean) adapts the
pinned v3 natural-merge/BitVec argument, using native v2 clearing arithmetic and
separate whole-word bounds at default recursion and heartbeat limits. No native
v3 field, column, table, key, selector or mapping premise is copied.
[The native connection](Airbender/Proofs/SubwordMemory/StoreData.lean) reconstructs
both actual packed keys and clearing/placement outputs from bounded actual reads.
Disjoint contributions cannot wrap Mersenne31 or carry beyond the selected limb.
The accepted native size/upper muxes and actual write equations then give the
complete merged word and each changed/preserved byte. SB selects exactly the
low source byte at any of four positions; SH selects the low source halfword at
either aligned position. Original decoding and the native offset mask derive
SH alignment. Complete literal table domains, including unused/odd rows, remain
unchanged; no aligned-domain table replacement is used.

[Initialized assembly](Airbender/Proofs/Trace/Families/SubwordMemory/StoreData.lean)
extracts both actual data-port and old-word-port read bounds from accepted history.
[One short public claim](Airbender/Review/Trace/Families/SubwordMemory/Stores.lean)
uses the same original public state for initialization and full sparse decoding.
No expected source/old word, range, alignment, selector, packed-key identity,
written value, table equivalence or intermediate state is supplied. Review adds
only the actual old-word observable, byte-window result and short theorem;
calculation and proof assembly remain under Proofs.

[Eight unchanged complete native traces](Tests/SubwordStoreData.lean) pass the new
claim, preserving all original memory/state matches and public code/seed reads.
Concrete accepted SB at offset three changes 0x89cd4567 to 0xabcd4567 from source
0xdead12ab; accepted SH changes it to 0x89cd12ab. Nonzero high source bits are
discarded and unselected old bytes are preserved. All-input byte correctness is
kernel proved, rather than inferred from these examples.

Next work connects these derived load/store values and addresses to actual
architectural memory/ROM read-write history, original Sail access/exception
behavior, native PC/prepare/retire behavior and full original subword execution.
The accepted odd LH-to-x0 case still has an open original exception comparison;
this store-byte checkpoint does not resolve or reclassify it. Delegation/custom/
CSR, unified execution, initialization/teardown and terminal/padding boundaries
remain unfinished. General Rust/JSON/compiler refinement and physical verifier/
cryptographic enforcement remain separate. FINDINGS and its exact historical
archive are unchanged, with zero confirmed native defects. Resource ceilings
are unchanged, the original checkout is preserved and nothing is pushed.
