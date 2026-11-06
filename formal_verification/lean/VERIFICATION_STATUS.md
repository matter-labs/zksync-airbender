# Verification status

**Checked** means kernel-checked claims over imported v2 native constraints
and logical matching under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [backport plan](FORMAL_VERIFICATION_PLAN.md). V3 results are source material,
not completed v2 coverage.

## User priority: native reduced machine (2026-10-21)

Work directly on the [actual combined reduced circuit](../../cs/reduced_machine_preprocessed_layout.json)
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
imports 117 native equations, 142 variables and a complete fourteen-region fixed
pool. Original Clean acceptance derives its two actual sign/high-byte queries.
The public fixture is explicit; general public configuration and other operation
semantics, initialized execution and global/physical enforcement remain open.
The historical 119-equation/141-variable/13-region artifact is preserved separately.
It is not assumed to be the current source-generated machine. Stage-two source
descriptors remain opaque. These are coverage/fidelity results, not native defects.

## Current v3 adaptation (2026-11-06)

[The adaptation snapshot](V3_ADAPTATION.md) pins PR #585 at
b29277dd895499574e317a994fd89243a72f06cb and distinguishes its unified CPU from
the reduced unrolled assembly. Five shared modules are copied unchanged from
that revision, including four arithmetic proof modules with transparent capacity
names. Original Clean and pinned Sail instruction semantics remain unchanged;
no v3 field encoding, native compiler certificate, finding, fix or machine
soundness result is inherited.

The structural reduced checks cover every tagged query field/table and actual
argument coordinates. The complete source bytes are retained. The complete serial bounded pass covers 777 source/test modules, including
139 test modules; 492 existing importer controls and 44 reduced/request
controls pass, as do all seven native CLI inputs, native exporter checks,
2,306 axiom roots and all 137 public Review claims. Dependency fingerprints
retain only unchanged verified modules. Peak charged footprint was
1387.39 MiB and peak resident usage 3601.03 MiB, below the unchanged
3072/4096 MiB ceilings. Every guard completed without a live owned process.

The independent bounded provenance audit also passes: 75 legacy and five
current byte-identical sources, seven native circuits, 56 native sources,
21 setup artifacts, four exporter files, 189 v3 adaptation identities and
693 earlier v2 reuse identities. Current architecture references and
historical reuse origins match their exact Git objects. The original
checkout and dependency versions are unchanged. The immediate next connection is actual native reduced
fixed/setup regions and public ROM/CSR configuration, then combined native row
semantics, initialized execution, worker/caller accounting and terminal/padding
boundaries. Existing five-family standalone execution remains separate.
A new hourly continuation task is active at the user's request; the previous
task remains paused. Production circuit code stays unchanged; confirmed issues
require documented evidence and explicit narrow interface assumptions.

## Reduced sign/high-byte fixed region (6 November 2026)

[The native reduced region](Airbender/Review/Circuits/ReducedMachine/Tables/SignHigh.lean)
now has a kernel certificate for all 65,536 literal rows: bounded key, exact
sign and high byte, and the actual ID-16 tag. The FV-only exporter calls the
unchanged registered native generator and retains compiled offset 196609.
The certificate reads the imported affine/periodic blocks symbolically at the
default Lean recursion and heartbeat settings. It assumes no table recipe or
expected outputs. Membership here is in the exported region; recovering it from
the full pooled setup, public ROM/CSR configuration and tag isolation remain open.

All seven new modules and the expanded axiom module passed targeted bounded
compilation. Eleven semantic regressions cover geometry, byte/sign boundaries
and wrong key/sign/high-byte/tag rejection. Seventeen runtime importer controls
pass, including a check that geometry validation alone does not assert contents.
All 39 native-export reproducibility/input checks pass, including the new region.
The complete axiom audit passes 2,320 roots using only Lean's standard three,
and all 138 public Review theorems have explicit audit roots. The successful
regional proof used at most 1496.76 MiB footprint and 3574.66 MiB resident;
resource ceilings were unchanged and no live owned process remained.
The earlier complete intake pass above is retained as its own checkpoint;
unchanged ordinary-family builds were not repeated for this isolated addition.
No production circuit code changed, no native defect was established and no
new interface assumption was introduced.

## Regenerated native reduced target and complete pool (6 November 2026)

Fresh compilation of the unchanged pinned native Rust differs from the shipped
historical JSON. It produces 112 quadratic/five linear equations, 142 logical
variables, witness width 107 and 5,771,521 generic rows, including native
truncation ID 47 at offset 5,705,985. The historical JSON has 114 quadratic/five
linear equations, 141 variables, width 106 and 5,705,985 generic rows. Source,
configuration and both artifacts are retained explicitly; the old file is not
rewritten and their accepted relations are not assumed equivalent.

[The full native table](Airbender/Review/Circuits/ReducedMachine/Tables/Native.lean)
reads all fourteen actual exported regions, with all four fields and no added
row. Its public fixture retains eight image words, delegation CSRs 1988/1989
and the native enabled nondeterminism setting. Independent native CLI cases
also check changed and empty public images/allow-lists and actual UNIMP padding.
Literal blocks are split into small declarations at default recursion and
heartbeat limits. No production circuit or machine code changed.

[Tag isolation](Airbender/Proofs/ReducedMachine/NativePool.lean) proves each
region's actual fourth column and recovers the certified sign/high-byte region
from complete pool membership. The short [native row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
then derives bounded keys, signs and high bytes for both constant queries from
original Clean acceptance of the regenerated constraints. The six full query
fields, common table, setup extent and changed initialization/request coordinates
have independent [mechanical checks](Airbender/Proofs/ReducedMachine/NativeArtifactChecks.lean).
No table-equivalence, desired-output or per-row numerical premise is supplied.

Validation passes for targeted native modules, the expanded axiom module and
historical import/emission regressions. All 592 importer controls pass
(492 existing, 44 historical reduced, 17 sign/high-byte and 39 current native),
as do all eight CLI inputs and 47 native compilation/export/input controls.
The complete audit passes 2,353 axiom roots using only Lean's standard three,
all 140 public Review theorem roots, guide links and layer separation. Provenance
checks 80 byte-identical reused modules, seven historical plus one regenerated
circuit artifact, 60 native sources, 23 setup artifacts and four exporter files;
189 v3 source identities and 700 earlier backport identities remain exact.
The original checkout and dependency versions are unchanged. Successful bounded
checks stayed at or below 1497.71 MiB footprint and 3576.36 MiB resident; limits
were unchanged and no live owned process remained. Unchanged ordinary execution
modules retain their prior complete checkpoint, rather than a repeated broad build.

The fixture does not establish arbitrary public ROM/CSR construction, semantics
of all other tagged operations, physical setup, compiler refinement, decoder
membership, initialized histories, delegation accounting or execution soundness.
Those remain the next native-machine obligations. The historical checkpoint
continues to have exactly its previous conditional meaning.

## Native dynamic selector domains (6 November 2026)

The [native row theorem](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives the domain of every one of the four dynamic lookup selectors from
original Clean acceptance. The fourth field remains the actual evaluated witness
expression. Complete pooled membership proves its canonical value belongs to the
fourteen actual native IDs; no per-row selector premise or extra disabled row is
introduced. An absent-ID-32 query is rejected by the checked complete pool.

Seven affected modules, including the expanded axiom module, pass direct serial
bounded compilation with explicit correct output paths. The complete audit now
passes 2,358 roots and all 141 public Review theorems, with standard axioms only.
The selector proof checks used at most 530.52 MiB footprint and 3048.59 MiB
resident, with unchanged limits and no owned survivors. Native generated inputs,
public configuration and operation semantics are unchanged, so the preceding
592 importer/eight CLI/47 native export controls remain the relevant checkpoint.
Operation-specific selector identities, flags, operand routing and results still
need proofs against the actual native constraints.

## Native reduced shift routing and truncation (6 November 2026)

The [short native claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now covers all six SLL/SLLI/SRL/SRLI/SRA/SRAI packed-mask cases on the regenerated
combined machine. All eighteen mask-bit bounds and the exact natural packed sum
come from original native equations. A supplied decoded packed mask determines
the twelve operation flags and rs2 routing; individual selector values are never
premises. The actual equations derive tags 47/37/37/20, the source-two
register/immediate route, its low-limb bound, exact modulo-32 shift amount and
unused third-field zero. These are local row facts, not instruction soundness.

[Tag isolation](Airbender/Proofs/ReducedMachine/NativePool.lean) now recovers any
selected literal region. The [native truncation certificate](Airbender/Proofs/ReducedMachine/NativeTruncation.lean)
checks definitional equality of actual stored columns with the previously
certified truncation columns; offsets remain distinct. It reuses the unchanged
symbolic row lemma with no table-equivalence premise. Calculations live under
Proofs; the [Review row model](Airbender/Review/Circuits/ReducedMachine/Row.lean)
contains only mask references and actual observables.

[Six regressions](Tests/NativeReducedShift.lean) reject oversized keys, wrong
remainders and nonzero unused fields, recover immediate-last/register-zero limb
boundaries and exclude standalone sign-fill tag 52 from this machine's tag-20
slot. The affected modules, all 2,378 axiom roots and all 143 public Review
theorem roots pass with unchanged watchdog limits. The largest affected proof
used 837.17 MiB footprint and 3055.92 MiB resident; the complete Review gate
used 536.33/3077.67 MiB. Every guard finished without owned survivors. No production source, generated native input or
public fixture changed; the preceding 592 importer/eight CLI/47 native controls
remain applicable rather than being regenerated without changed inputs.

The decoded mask is still an explicit input. Original public decoding must derive
it before initialized execution can use this claim. Shift table-37/sign-fill
semantics, results, actual masked writes, PC effects, other operations and the
remaining machine/protocol boundaries remain open. No new native defect or
issue-handling assumption is introduced.

## Native reduced arithmetic-shift filler (6 November 2026)

The [native row claim](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now derives the actual sign-fill word and both output-limb bounds for all six
shift-mask cases. The three minor bits come from accepted Boolean/packed-mask
constraints, not supplied control answers. The actual fourth dynamic query is
recovered from equations 94/95/96 and its derived tag 20. Native constant queries
supply the high-limb sign; truncation supplies the bounded amount. Canonical
field arithmetic recovers the complete seven-bit key without an extra bound
premise. The public decoded-mask input remains explicit.

The [literal certificate](Airbender/Proofs/ReducedMachine/NativeSignFill.lean)
checks all 128 actual tag-20 rows and their output bounds in the kernel. The
[reference](Airbender/Review/Circuits/ReducedMachine/Tables/Shift.lean) retains
original native sign/control/amount packing and the explicit zero-shift case.
[Reference calculations](Airbender/Proofs/ReducedMachine/SignFillReference.lean)
and [row assembly](Airbender/Proofs/ReducedMachine/NativeShiftFill.lean) stay under
Proofs. Eleven [regressions](Tests/NativeReducedSignFill.lean) cover shifts
0/16/17/31, positive/logical controls, wrong filler rejection and actual selected
row boundary consequences. The affected modules and complete axiom/Review gates
pass: 2,398 explicit axiom roots, 145 public Review roots and all guide/layer
checks. The largest successful affected proof used 838.72 MiB footprint and
3073.80 MiB resident; the complete Review gate used 539.61/3085.50 MiB. All
completed without owned survivors under unchanged resource caps.
Native setup/compiler/importer inputs did
not change, so the preceding 592 importer/eight CLI/47 native controls remain
applicable.

The attempted table-37 cross-artifact column comparison exceeded the existing
resident or Lean allocation limits; every owned process terminated. Even a
small slice through the whole imported column required a different evaluation
strategy. Its unverified draft is excluded from the source tree and coverage.
Table-37 meaning, contribution assembly, full results, masked writes/PC, public
decoding and initialized execution remain open. This resource boundary is not
a native circuit defect, table-equivalence premise or new interface assumption.

## Native reduced contribution writes and PC selection (6 November 2026)

The [short native claims](Airbender/Review/Circuits/ReducedMachine/Theorems.lean)
now recover both actual tag-37 queries, including the native direction/amount/limb
keys and the actual output fields. [Query assembly](Airbender/Proofs/ReducedMachine/NativeShiftQueries.lean)
uses original Clean acceptance and derived direction/tags; it does not supply
membership, table equivalence or arithmetic output answers as premises.

[Actual port observables](Airbender/Review/Circuits/ReducedMachine/ShiftWrite.lean)
retain the imported source-one read, mixed destination address, destination write,
rd/zero-flag coordinates and outgoing PC. [Metadata checks](Airbender/Proofs/ReducedMachine/NativePorts.lean)
bind their real columns. [Header recovery](Airbender/Proofs/ReducedMachine/NativeShiftHeader.lean)
derives the update/no-source bits. [Native equation assembly](Airbender/Proofs/ReducedMachine/NativeShiftWrite.lean)
then derives left/right cross-limb selection, inactive load zeros, the candidate,
actual zero-flag masking and destination register-space address. The actual final
PC selects the native default-PC candidate. These statements need no expected
write, source-range or successor-PC premise.

[Eight conditional regressions](Tests/NativeReducedWrite.lean) cover discarded
writes with both queries retained, rejection of nonzero discarded writes,
left/right cross-limb assembly, arithmetic zero-shift filler and either outgoing
PC limb mismatch. They are consequences of original native acceptance, not
complete accepted execution fixtures. The affected bounded modules and complete
axiom/Review gates pass: 2,420 explicit axiom roots and 148 public Review roots,
with exact provenance and guide/layer checks. All owned workers terminated under
the unchanged allocation, footprint, resident and wall-time limits. No circuit,
compiler/importer input or literal pool changed; the preceding 592 importer,
eight CLI and 47 native controls remain applicable.

Table-37 arithmetic meaning remains unverified. This milestone proves assembly
of its actual output fields, not their numeric shift result. The explicit packed
mask, original public decoding, architectural rd/x0 connection, initialized source
reads, numerical PC+4/wraparound, combined Sail execution, workers and protocol
boundaries remain open. The earlier failed large table-37 checks were not retried.
No defect, circuit fix or new interface restriction is introduced.

## Complete native reduced shift-column transport (6 November 2026)

The [actual column certificate](Airbender/Proofs/ReducedMachine/NativeShiftColumns.lean)
now checks both output columns for every index in the 4,194,304-row native tag-37
region. It derives exact getter equality to the previously certified native
SLL-low/SRL-high columns. The right half reverses the earlier split table's two
output columns. A [symbolic boundary proof](Airbender/Proofs/ReducedMachine/ShiftBlocks.lean)
retains the native merger of 1,048,576 left-half zeros with the first right-half
zero and the remaining 65,535 ascending values. No table-equivalence premise,
new setup fixture or native generation is introduced.

Twenty independently emitted periodic blocks are identified with the existing
certified templates. Literal structure is reduced before small, complete
64-value kernel checks; geometry is handled symbolically. Eight bounded block
assemblies cover all 148/291 actual output blocks. The
[reference shapes](Airbender/Proofs/ReducedMachine/NativeShiftReferences.lean)
retain exact prior source hashes, and all proof calculation stays under Proofs.
The largest successful template used 530.09 MiB footprint/2867.55 MiB resident;
full column composition used 499.67/2819.36 MiB. No proof limit was increased.

The affected bounded modules and complete axiom/Review/provenance/guide gates
pass: 2,459 explicit standard-only axiom roots and 148 public Review roots. The
existing public row surface is unchanged. Native data, exporter/importer inputs,
production circuit/Rust and dependencies remain unchanged; the prior 592
importer, eight CLI and 47 native controls remain applicable.

This closes the large literal-column identity gap, not the complete numerical
row/query or instruction theorem. A combined second-output numerical assembly
still exceeds Lean's allocation cap despite separately checked native transport,
old arithmetic and small reference identities. Its draft is outside the source
tree and excluded from coverage. Every failed/limited worker terminated without
survivors; no ceiling was raised. Canonical pooled numerical query results,
source/key binding, complete shift words, public decoding/rd/x0, numerical PC,
initialized execution and machine/protocol boundaries remain open. Resource
failures and unfinished composition are not native defects or new interface
assumptions.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | Conditional ADD/ADDI/SUB/LUI/AUIPC destination and original Sail PC/register effects. Packed native masks derive the eight selector bits. The actual masked destination write is observed. Aligned PC wraparound and discarded x0 writes are included. |

| Integration | Coverage |
| --- | --- |
| [Jump/branch/SLT fixed effects](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | All 36 native equations, six scalar/eight timestamp/two fixed queries and exact metadata imported. Actual cleanup/conditional table certificates derive key bounds and exact native control/cleanup values; full active JAL witness and alignment rejection checked. Supported native masks now derive both outgoing PC limb bounds; the JAL -4 negative-high witness shape fails an actual scalar query. Public decoding is checked below; initialized history and cell transfers are checked below; original Sail instruction/trace execution remains open. |
| [Public control decoding](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean) | Actual public bytes and original Sail decoding construct a full sparse/padded ten-column table. Native equations reject holes/tail, recovering supported masks, canonical inputs/alignment and exact x0 flags; the short native claim derives outgoing PC bounds without a mask/range premise. Separate SLTI/branch masks, retained x0 operations and raw JAL funct3 are checked. Concrete native program export and initialized native history are certified below; original Sail instruction execution and terminal instruction-state matching remain open. |
| [Initialized native control history](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) | The separate native clock/port registry proves the shared clock contract from actual control equations/queries. Public Sail seeds/PC and complete native matching derive every row/prior clock, complete Clean history and newest reads for all three ports, retaining readonly alias refreshes and actual masked writes. Control word bounds and Sail cell transfers are checked below; original instruction execution remains separate. |
| Initialized control values/cells | [Word bounds](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean) derive every native read/write/terminal range from actual public sparse decoding and initialized matching. [Sail cell history](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean) derives all intermediate cell states in native clock order, including x0 preservation from actual masks. Original control instruction execution and terminal instruction-state matching remain open. |
| [Initialized control register transfers](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean) | Original public decoding and native clock-ordered history derive all original source/destination GPR reads and the actual masked write at constructed row boundaries. Both source reads and the old destination read use one cell-history pre-state, including aliases. Original control clauses, native operation semantics and PC retirement remain open. |
| [Native saved jump links](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) | Full original public decoding and every native constraint derive the actual JAL/JALR PC+4 write, including discarded x0. Native mask classification recovers selectors; actual scalar ranges and Boolean carry equations prove RV32 addition. Exported-JAL, logical JALR/x0, local full native wrap and altered-write rejection regressions pass. Target calculation is checked below; original control instruction execution remains open. |
| [Initialized native jump targets](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean) | Actual public bytes, initialized matching and native equations derive every JAL/JALR target and four-byte alignment, including JALR bit-zero clearing. Source/PC/immediate bounds, original JAL parity, selectors and carries are derived. The exported negative JAL and initialized aliasing JALR pass; full original instruction execution/retirement remains open. |
| [Initialized native comparison results](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean) | Native equations, actual scalar/fixed queries, original public metadata and initialized matching derive all four SLT/SLTU/SLTI/SLTIU masked results. Operand ranges, selector identity, signs, borrow and x0 mask are derived. Signed/unsigned disagreement and negative-immediate/x0 regressions pass; branch semantics and original full instruction execution remain open. |
| [Native comparison PC advancement](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean) | Actual public decoding and native acceptance derive PC+4 and four-byte alignment for all four comparisons. Native scalar ranges supply both outgoing bounds, Boolean carries retain RV32 wrap and raw candidate routing is preserved. All four initialized fixtures, full local wrap and altered-PC rejection pass; original Sail retirement and branch semantics remain separate. |
| [Initialized native branch conditions](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean) | Original public decoding and initialized matching derive all six branch conditions, equality/sign/borrow flags, both routing bits and actual zero writes. Native inverse equations identify equality and actual scalar/fixed queries resolve signed/unsigned order. Eighteen initialized cases cover both outcomes per opcode; branch targets and original Sail retirement remain separate. |
| [Initialized native branch targets](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean) | The checked six conditions select PC+offset or PC+4 with RV32 wrap and four-byte alignment. Original public decoding derives parity, incoming bounds/alignment and selectors; actual native carry, range, routing and cleanup constraints determine both outgoing limbs. Eighteen initialized cases, local negative/wrap rows and taken-only alignment rejection pass; original Sail clauses/retirement remain separate. |
| [Initialized original comparison execution](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) | Exact original SLT/SLTU/SLTI/SLTIU clauses and shared preparation/retirement reach native output PCs in constructed initialized-history segment states, including retained x0 source reads and discarded writes. All four original-byte fixtures execute from actual public states; full fetched control composition/terminal matching and original jump/branch clauses remain separate. |
| [Initialized original branch execution](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean) | Original BEQ/BNE/BLT/BGE/BLTU/BGEU clauses prepare and retire to exact native targets in constructed initialized-history segments. Actual public misa readability is explicit, with unrestricted value and history-derived CSR preservation. Eighteen unchanged native fixtures execute both outcomes per opcode from configured public states and derive complete data-state stuttering. Original jumps and full fetched control composition/terminal matching remain separate. |
| [Initialized original jump execution](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean) | Original JAL/JALR clauses retire to native targets and actual masked link writes in constructed history segments. Actual initial misa is readable; traces containing JALR use Machine privilege and MLPE-clear mseccfg, transported through history. The existing negative JAL and aliasing JALR execute from public states, reaching 0xfffffffc/link four and 264/link eight. JAL needs no privilege/security entries. Full fetched control composition/terminal matching remains separate. |
| V2 artifact import | All 34 quadratic and 3 linear equations, four 16-bit and eight 19-bit timestamp queries from the pinned ADD/SUB layout. Bounds/placement guards and both native zero coefficient encodings. |
| Reused foundation | Unchanged property definitions, word representation/arithmetic and pinned Sail reference/execution lemmas. Source hashes are checked. |
| Native state/port clocks | Typed physical state and three direct ports, including actual destination writes. Four-tick advancement and strict previous-write/port order follow from imported equations/queries under initial/prior clock bounds and alignment. The initialized-history layer now derives these local inputs from matching and initial boundaries. |
| Initialized logical memory | Accepted native state/memory matching, initial clock bounds/alignment and unique seed addresses construct complete Clean online consistency, per-address paths and newest preceding reads. Readonly refreshes and actual destination writes are included. Public Sail seed/initial-PC construction is checked separately below. |
| Public initial image | Actual Sail register/RAM and PC reads construct native seed tokens and initial PC at native clock four. Missing registers/bytes reject construction. Seed word/clock bounds and address uniqueness follow; no per-row values or clocks are supplied. Physical boot/profile remains separate. |
| Native decoder placement | Ten-column v2 query order, separate rd-zero flag, packed mask and actual memory/witness bank placement are imported and mechanically checked. Unsupported extra descriptor fields fail closed. Selected-profile construction and logical membership are checked below; generation/export remains separate. |
| Public decoder setup | Actual public bytes and pinned Sail decoding construct selected five-opcode rows at PCs 4*i with power-of-two capacity and the complete native-shaped minus-one tail. Missing/unsupported/effectful entries fail. Native packed-mask equations exclude padding before logical membership recovers public source evidence, zero flags and canonical PC/immediate words. Rust generation/export fidelity remains separate. |
| Initialized native word bounds | Public Sail seeds, accepted matching/clocks and complete decoder membership derive every native read, actual masked write and terminal word bound. No per-row bounds or flag answers are supplied. |
| Native-to-Sail history | Public seeds, native matching and complete decoder membership derive actual Sail cell reads/writes and all intermediate states. Native masked writes preserve x0 without v3 NOP preprocessing. Public RAM-cell alignment supplies disjoint byte windows. Native clocks derive row ordering/grouping and readonly refreshes stutter even with aliases; decoder indices identify actual Sail GPR reads/writes. Instruction execution is checked below. |
| Native PC path | Successful public setup retains its indexed PCs and derives every incoming bound/alignment through RV32 truncation. Native carry/wrap equations derive bounded outgoing successors; state matching and the actual public initial PC bound the terminal PC, including empty traces. No per-row PC premise is supplied. Actual Sail retirement and complete execution are checked below. |
| Decoded arithmetic row retirement | Proof-layer assembly derives mask/zero flag, preprocessing, operand/immediate bounds, original Sail reads, PC facts and native observable mapping for all five arithmetic opcodes. Original Sail normal preparation/execution/retirement reaches the actual masked native write. Control-register commutation supplies rebased PC reads. No erased-source or per-row numerical premise is added to the initialized assembly. Complete trace composition is checked below. |
| Initialized arithmetic execution | Public Sail state and selected five-opcode setup, accepted native constraints/state/memory matching and public RAM alignment derive a finite original Sail normal-path trace to exact terminal PC/register/RAM values. All row order, reads, bounds, selectors, preprocessing, intermediate states and retirement effects are proved. Actual code-byte reads and pure original decoding are preserved across native GPR updates; empty traces are included. Physical setup/argument enforcement remains separate. |
| [Word-memory native transfers](Airbender/Review/Circuits/WordMemory/Theorems.lean) | All 31 quadratic/four linear equations, two scalar/eight timestamp queries and both fixed three-column ROM queries are imported. Three native ports and all decoder columns are checked. Complete native-shaped separator/ROM tables derive canonical aligned address limbs, exact ROM data, mixed port selection, masked RAM/ROM loads and RAM-only stores. The native Mersenne31 source-plus-immediate address calculation derives both carries and RV32 wraparound from explicit source/immediate bounds. PC bounds/alignment and native clock inputs yield modular PC successors, four-tick advancement and strict port order. Public decoding and initialized logical history/ranges are checked below; actual Sail cell transfers are checked below for the full supplied native image; architectural projection is checked separately below, while original instruction execution is checked below; physical boot/padding/ROM binding remains open. |
| [Word-memory public decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean) | A separate checked native registry and original public LW/SW bytes construct complete padded setup. The native Boolean store mask rejects padding before membership recovers actual Sail source evidence, exact rd-zero flags, canonical register indices, immediate/PC bounds and incoming alignment. Sign extension and original x0 loads are retained. Logical ranges and actual Sail cell histories are checked below. Instruction execution is checked below; architectural boot/padding/shadow-state binding remains open. |
| [Public ROM image/read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) | Original Sail byte reads construct a length-preserving ROM vector; excessive counts and missing bytes fail. Native table data is recovered as an actual Sail read inside the extracted prefix. A complete 1048576-word extraction derives coverage of every native ROM address. Full native UNIMP padding is retained; no expected-read/table-equivalence premise is supplied. Supplying Sail boot/padding/shadow state and proving physical setup/export remain separate. |
| [Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean) | The native clock instance reuses shared matched-clock recovery and complete Clean history/latest-read proofs for every native port. Actual public seed/PC reads discharge initial clocks, ranges and unique addresses; no per-row clock/read/order premise is supplied. Readonly ROM-shadow accesses remain participating native accesses. Their architectural projection has a separate checked claim below. |
| [Word-memory value ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean) | Native load/store/mask equations preserve word bounds through earlier port copies or canonical ROM data. Full padded decoder membership recovers the zero flag. The unchanged shared decreasing-time induction derives every read, actual write and terminal word bound from actual public seeds and matching, including discarded shadow reads and x0-masked writes. Actual Sail cell transfers are checked below for the supplied native image; the separate projected history is checked below; Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Initialized word-memory native effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) | The first native port's initialized range and actual public decoder setup discharge every local numerical input to the existing native address/PC/clock calculations. Effective-address addition, bounded aligned incoming PCs, bounded RV32 PC successors and four-tick/port-order laws follow, retaining wraparound. No per-row range, carry, PC, clock or desired effect is assumed. Actual Sail cell transfers are checked below for the supplied native image; the separate projected history is checked below; Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Word-memory Sail cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean) | Mixed-port equations and full decoder membership prove hardwired x0 preservation. Shared Clean-to-Sail realization and native row grouping derive actual cell reads/writes, intermediate states and final cell matching from the supplied public seed image and public RAM alignment. Readonly refreshes preserve the instruction pre-state; decoder metadata identifies the original Sail source GPR. This retains all native shadow cells as tracked RAM; a separate checked projection below omits shadows. Original instruction execution is checked below; physical boot/ROM binding remains open. |
| [Native shadow value preservation](Airbender/Review/Circuits/WordMemory/Theorems.lean) | Every imported native RAM port mapped below the four-MiB ROM boundary preserves its exact raw value code. Full constraints and port metadata exclude final-port stores there; the first two ports only refresh timestamps. No initial Sail image, expected value or ROM-byte equivalence is assumed. Full native matching retains all shadow tokens; the separate projected architectural history is checked below. |
| [Architectural word-memory projection](Airbender/Review/Trace/Families/WordMemory/Projection.lean) | Whole-address restriction preserves original Clean online consistency and latest values. Public initialization reads only architectural GPR/RAM cells and retains independently supplied canonical native shadow seeds. Native clocks/unique addresses, x0 writes, row order, actual Sail cell transfers and final architectural matching follow while the complete native memory history retains all shadow seeds/accesses. The unchanged shared range induction also derives every full native read, actual write and terminal word bound, including erased shadow accesses. No shadow/Sail read, per-port bound or shadow/ROM equality is assumed. Original instruction execution is checked below; physical native boot/profile and ROM-table binding remain separate. |
| [Projected word-memory row interfaces](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) | Separate architectural/shadow initialization, actual public decoding and full native matching now derive effective-address addition, bounded aligned native PCs, modular successors and native clock/port effects. Shared readonly-prefix transport recovers every retained Sail port read in the instruction pre-state and the actual final masked write. Full native constraints prove that the final port always targets a GPR or RAM outside the ROM prefix. Native shadow matching is retained without Sail shadow reads. Original LOAD/STORE execution/retirement is checked below; physical boot/ROM binding remains separate. |
| [Word-memory code/ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean) | Initialized projected transfers preserve every byte below four MiB, including missing bytes and code outside tracked cells, and every successful public ROM extraction. Native constraints and projected cell realization keep actual stores outside this region. For public programs fitting the native ROM region, indexed setup construction supplies complete code-byte windows and original Sail reads/decoding survive every prefix. A real changing RAM store and dependent load retain code/ROM evidence without later-read, intermediate-state or desired-value premises. Original instruction execution is checked below; physical boot/export remains separate. |
| [Word-memory platform configuration](Airbender/Review/Trace/Families/WordMemory/Platform.lean) | Initialized projected histories preserve the public original Sail Machine/PMP/PMA configuration. Eight platform modules are copied unchanged from the pinned source. Native RAM address/port equations derive actual Sail reads/writes and alignment; unchanged Sail translation, permission and ordinary-memory helpers transport those effects into actual virtual-memory calls. The dependent native SW/LW regression derives a virtual store and later read of 123 with no supplied intermediate state/read/result. Public ordinary-address and configuration conditions remain explicit. Original clauses and row preparation/retirement are checked below; complete trace composition is checked below; physical boot/export remains separate. |
| Original word-memory clauses | [ROM transport](Airbender/Proofs/Trace/Families/WordMemory/ROMTransport.lean) composes actual public byte extraction, retained source reads, native address/alignment and preserved configuration into original Sail virtual ROM reads. Native ROM bounds derive ordinary addresses. [Clause assembly](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean) derives the original unmasked destination effect from native masked writes, including original x0 without NOP projection. [Initialized regressions](Tests/WordMemoryROMTransport.lean) construct real decoder/ROM bytes and reach original LW clause results in the same actual native after-state, with full shadow matching and shadow value 123 distinct from actual ROM word 0xc0001073. [RAM clause assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean) derives load/store selectors and original registers/immediate from the public decoder, actual rs2/RAM reads from retained ports, and original RAM LW/SW results in the actual cell-transfer states. [The reversed dependent fixture](Tests/WordMemorySailHistory.lean) reaches original SW then LW results with actual read 123 and actual destination write, without an intermediate state/read/result premise. Ordinary-address and configuration conditions remain explicit. Row preparation/PC retirement is checked below; complete word-memory trace composition is checked below. |
| Decoded word-memory row retirement | [Original clause selection](Airbender/Review/Helpers/Decoder/Instruction.lean) reuses the pinned dispatcher without v3 discarded-load deviations. [Retirement](Airbender/Proofs/Trace/Families/WordMemory/Retirement.lean) transports actual histories, configuration and ROM bytes through original nextPC preparation and tick_pc. [Native assembly](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean) derives effective addresses and exact modular native PC successors from initialized matching/public decoding, selecting original RAM LW/SW or ROM LW. No prepared read/state or desired PC result is assumed. Ordinary/x0 ROM regressions retire to native PC 4; reversed dependent SW/LW normal steps derive actual PC 8 and terminal RAM/x3 values 123. Local ordinary-RAM and extracted-prefix coverage domains remain explicit; complete finite trace/fetch composition is checked below; physical boot/export remains open. |
| Range tables | Actual native range16/timestamp19 prefixes and modeled active zero fill have exact unchanged Clean static-table meanings. The reserved normalization row, physical multiplicities and Rust trace/LDE refinement remain separate. |

## Remaining work

- Generalize native export certificates to arbitrary public programs and refine the checked complete row model against Rust trace construction; connect physical initialization and expand mixed/custom programs.
- Extend initialized execution to shift/binop and the remaining supported families; preserve each native metadata and argument boundary. Complete standalone control and unsigned MUL/DIV execution are checked below.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed tables, dynamic selector profiles beyond the four native shift/binop witnesses, unpaired byte ranges and inter-row linkage are rejected by the importer.

## Initialized word-memory execution

[The short public theorem](Airbender/Review/Trace/Families/WordMemory/Theorems.lean)
proves [finite original Sail execution](Airbender/Review/Trace/Families/WordMemory/Execution.lean)
from actual public state, decoder/ROM extraction, full accepted native matching
and public domains. It checks actual code-byte reads and original decoding at
every instruction, then normal preparation, LW/SW and retirement. Exact native
terminal PC and architectural terminal cells follow from full native history.
Shadow tokens remain matched independently; their values are not Sail ROM bytes.

[Address-domain assembly](Airbender/Proofs/Trace/Families/WordMemory/AddressDomain.lean)
roots each effective address in public cells or public shadow seeds. Ordinary RAM
and coverage by the actual ROM prefix are public domain conditions; no per-row
range, read, order, intermediate state or desired result is supplied. Public
Machine/PMP/PMA configuration and program size within ROM remain explicit.
[Composition](Airbender/Proofs/Trace/Families/WordMemory/Composition.lean) preserves
code, pure decoding, configuration and actual ROM extraction through every
realized prefix. Empty traces preserve actual PC and cells. Physical boot/padding,
setup/export, mixed families and cryptographic enforcement remain separate.
Architectural fetch permissions, exceptions and interrupts remain outside this
successful-step reference relation.

## Fixed native boot and padding paths

[The short native-boot theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
replaces arbitrary initial values/PC reads with the unchanged original Sail
zero-initialization profile, native PC zero/time four and all-zero native seeds.
[Assembly](Airbender/Proofs/Trace/Families/WordMemory/Boot.lean) derives the existing
architectural/shadow initializer and complete original LW/SW execution. Actual
initial reads still come from Sail; missing cells are not defaulted.
[Full native paths](Airbender/Proofs/Trace/Families/WordMemory/BootShadow.lean)
force terminal shadows to remain zero without interpreting them as physical ROM.

Native source review confirms zero GPR/RAM initialization and address-preserving
zero witness masks below four MiB. The proving loader zero-pads its input word
image; the raw ROM table constructor retains UNIMP only beyond its supplied
image. [The separate padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean)
proves full extent, prefix retention and zero tail symbolically. The explicit
[loader constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) now
inserts actual zero bytes into Sail memory and derives complete four-MiB public
ROM extraction without evaluating a huge map/list. Prefix/outside bytes, all
registers, the original zero profile and public configuration are preserved.
Public decoder setup survives when its code fits the supplied prefix. The added
[short padded-boot theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean)
derives all ROM-shadow coverage from construction. Ordinary/x0 native fixtures
exercise complete original execution, byte boundaries and previously absent
zero reads; missing and excessive prefixes reject construction. Public alignment,
configuration, ordinary RAM and code-prefix inclusion stay visible. Physical
initialization/setup exports, Rust/compiler refinement and argument enforcement
remain open.

## Native setup geometry and tagged row model

[Imported setup placement](Airbender/Review/Helpers/Tables/SetupColumns.lean) now
covers the exact arithmetic/word-memory widths 12/16, scalar columns 0/1,
three-value-plus-tag generic groups, ten-column decoder groups, all 62 native
table offsets, decoder capacity and the final row reserved for normalization.
Malformed extents, overlaps, missing dummy rows and changed offsets fail closed.

[The native-shaped active row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean)
retains the dummy tuple, every separator/ROM tuple with native tags 23/24 and all
zero padding. [Symbolic proofs](Airbender/Proofs/WordMemory/PhysicalSetup.lean)
recover exact logical membership and reject wrong-table/dummy/padding tags.
[One short public read claim](Airbender/Review/Trace/Families/WordMemory/Setup.lean)
derives actual Sail words from tagged ROM membership after explicit loader
construction. A nonempty original-LW fixture proves original/padded reads and
altered-data rejection without expected-read or table-equivalence premises.
No large trace/map/list is evaluated. Actual regional native values are now checked
for the fixture below; general program construction, physical trace assembly,
normalization/LDE refinement and argument enforcement remain open.

## Actual native setup export

[The native exporter](../native_setup_exporter/README.md) now calls the pinned
v2 table driver, word-memory decoder materializer and range16 generator directly.
Its [9 KiB fixture](artifacts/setup/word-memory-native.json) retains separate
public image/text inputs, all 1,114,113 generic tuples with native offsets/tags,
all 1,048,576 decoder slots and all 65,536 scalar entries. Lossless compression
is checked against every materialized value before serialization. No full setup
trace, LDE or witness is built. [Literal import](Airbender/Import/SetupEmbed.lean)
and [symbolic certificates](Airbender/Proofs/WordMemory/NativeSetup.lean) check every
ROM/separator/range row, unsupported decoder tail and public image zero tail.
The short [exported-ROM read claim](Airbender/Review/Trace/Families/WordMemory/Setup.lean)
connects actual tagged exported rows to original Sail bytes after explicit padding,
with the actual four-word prefix extraction as its public input condition.
The original LW/SW/x0 prefix and explicit unsupported UNIMP slot are checked.
These certificates cover this pinned native fixture; arbitrary programs, arithmetic
native decoder certificates are checked separately below; full physical trace
padding/normalization/LDE, initialization and argument enforcement remain open.

## Sparse native decoder construction

[Sparse public decoding](Airbender/Review/Helpers/Decoder/SparseSetup.lean) now
reads every supplied word and retains unsupported pure decoder results as holes
at their original PCs. Missing bytes and effectful decoding reject construction.
The complete native-shaped minus-one tail is retained. [Recovery](Airbender/Proofs/Trace/Families/WordMemory/SparseDecoder.lean)
reuses the actual native Boolean store-mask equation to exclude both holes and
tail slots before deriving original Sail bytes/decoding, canonical PC/immediate
bounds, incoming alignment and the exact x0 flag. No per-row metadata or desired
result is supplied.

A [second actual native export](artifacts/setup/word-memory-holes-native.json)
places UNIMP between LW and SW/LW-to-x0. Supported PCs remain 0, 8 and 12.
[Public byte data](Airbender/Review/Circuits/WordMemory/Tables/NativeSparseData.lean)
and [certificates](Airbender/Proofs/WordMemory/NativeSparseSetup.lean) construct the
sparse setup through original Sail reads/decoding and prove every exported decoder
row equals its constructed row, including the interior hole and million-slot tail.
[Two short public claims](Airbender/Review/Trace/Families/WordMemory/SparseDecoder.lean)
cover general successful sparse construction and this pinned actual export.
[The nonempty regression](Tests/WordMemory.lean) satisfies every original native
row equation and lookup for an x0 load at PC 12 before recovering its original
public source through exported membership. Missing bytes/capacity and supported
post-hole fields are checked separately. The separate initialized execution claim
below now composes sparse decoding with full native matching. Arbitrary-program Rust decoder refinement and full physical
trace/argument connections remain open.


## Initialized sparse word-memory execution

[The short sparse execution claim](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean)
now derives the same finite original Sail LW/SW relation and exact native terminal
PC/cells from successful sparse construction and full accepted native matching.
Public initialization, configuration, actual ROM extraction, ordinary RAM and
ROM-prefix seed coverage retain their existing meanings. Native equations reject
holes/tail before selecting real entries; every original indexed PC is preserved.

[Internal constructor evidence](Airbender/Proofs/Trace/Families/WordMemory/ProgramImage.lean)
is derived from actual strict or sparse construction. Shared native numerical,
code-frame, original clause/retirement and terminal assembly then serve both
builders. The existing strict public claim is unchanged. The internal supported
entry list is only a proof selection index; the public sparse table keeps every
physical hole and no code byte or PC is rewritten. No per-row bound, source/read,
intermediate state, desired result or table-equivalence premise is introduced.

[The nonempty initialized regression](Tests/SparseExecution.lean) reuses the full
native x0-load witness and actual exported decoder slot three. Real public code,
registers, CSRs and RAM bytes plus complete native state/memory tokens derive
original fetched execution from public PC 12 to PC 16, unchanged RAM 123 and x0
zero. The unsupported word at PC four remains in the public image. The supplied
initial PC is 12; this does not assert control flow that skips an executed hole.
General Rust/Sail decoder agreement, arbitrary-program export certificates,
physical setup/initialization and cryptographic enforcement remain separate.


## Native shared scalar prefixes

[The separate scalar artifact](artifacts/setup/scalars-native.json) now retains
all 65,536 range16 and 524,288 timestamp19 values using two lossless affine
blocks. The standalone exporter calls the native range16 API and copies the
pinned prover's three-line timestamp generation clause unchanged, using the
native constant reexported by cs. The standard gate checks that exact clause
identity, every compressed value and byte-for-byte regeneration. No prover
build, dependency change or full physical trace allocation is required. Existing
program fixtures and their format are unchanged.

[Literal scalar data and active rows](Airbender/Review/Helpers/Tables/NativeScalarData.lean)
retain both actual prefixes, then model the native active zero fill. The final
normalization row stays outside this domain. [Symbolic certificates](Airbender/Proofs/Tables/NativeScalars.lean)
prove every prefix/filler row and exactly the original 16/19-bit range meanings,
then connect them to the unchanged Clean range helpers used by both circuits.
A [short shared scalar claim](Airbender/Review/Helpers/Tables/NativeScalars.lean)
adds no table-equivalence premise. Repeated zero filler is retained as valid
range data; this statement does not prove physical lookup multiplicities.

[Regressions](Tests/NativeScalars.lean) check both compiled column placements 0/1,
actual prefix endpoints, the first filler and last active row, exact regional
endpoints and out-of-range rejection. The importer rejects malformed extents,
widths, canonical values, unknown nested fields and incompatible profiles.
These are complete native regional data certificates plus a source-shaped
active-padding model. Formal Rust physical trace/normalization/LDE/argument
refinement and arbitrary-program certificates remain separate. The concrete
arithmetic decoder certificate is checked below.

## Actual native arithmetic decoder export

[The native arithmetic artifact](artifacts/setup/arithmetic-native.json) now
retains all 1,048,576 ten-column decoder slots from the actual v2 arithmetic
preprocessor/materializer. Its seven public words exercise ADD, signed ADDI,
SUB to x0, LUI/AUIPC with nonzero raw funct3 bits, an unsupported UNIMP word at
PC 20 and another ADD at its original PC 24. Existing program/scalar artifacts
and the unchanged exhaustive lossless codec retain their meanings.

[Independent public bytes and entries](Airbender/Review/Circuits/AddSub/Tables/NativeSetupData.lean)
feed original Sail reads and decoding. [Kernel certificates](Airbender/Proofs/AddSub/NativeSetup.lean)
construct the sparse setup and prove equality of every actual exported row,
including the interior hole and full tail. Native packed-mask equations exclude
both sentinels before [the short source claim](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean)
recovers original public evidence. Row equality is proved, never assumed.
[The regression](Tests/NativeArithmeticSetup.lean) checks all five field shapes,
public text identity and a complete native ADD row at PC 24 with actual exported
membership. Nineteen importer checks reject malformed and incompatible artifacts;
fixture and equivalent binary text reproduce byte for byte.

This is a concrete native-data/source certificate. General Rust/Sail decoder
agreement, arbitrary-program certificates, custom modular MOP semantics and
physical trace/argument refinement remain separate. Sparse initialized arithmetic
execution is now checked below. No instruction skipping an executed hole or new implementation defect
is claimed.

## Initialized sparse arithmetic execution

[The short sparse arithmetic claim](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean)
now derives original fetched/decoded ADD/ADDI/SUB/LUI/AUIPC execution and exact
terminal PC/cells from actual public initialization, successful sparse byte/Sail
construction and complete accepted native matching/decoder membership. Public
RAM-cell alignment remains visible. Native packed-mask equations reject every
unsupported hole and tail row before source selection.

[Internal indexed constructor evidence](Airbender/Proofs/Trace/ProgramImage.lean)
is derived from either actual builder. The existing arithmetic numerical,
original Sail clause/retirement, history/code-frame and terminal proofs then
serve both. The strict public theorem keeps its original statement. The supported
entry list is an internal proof index; all public code bytes and original indexed
PCs remain intact. No indexed-source, per-row bound/read, intermediate state,
desired terminal value or table-equivalence premise is added to the public claim.

[The nonempty regression](Tests/SparseArithmeticExecution.lean) selects actual
exported slot six at PC 24. Full native equations/lookups and complete aliased
x1-port matching derive the clock-four/five refreshes, destination read and actual
clock-six write. Original public bytes/decoding then yield execution to PC 28 and
x1=246. The UNIMP word at PC 20 remains in memory; public initial PC 24 does not
assert control flow skipping an executed hole. General Rust decoder agreement,
arbitrary-program export certificates, custom MOPs and physical trace/argument
refinement remain separate.

## Active native decoder setup rows

[The direct native padding export](artifacts/setup/decoder-padding-native.json)
now calls the same native decoder-padding API as physical setup assembly. Its
ten canonical Mersenne31 values are all minus one. Exact regeneration and twelve
strict importer checks preserve the separate parsing/emission fidelity boundary.
The native materializer comment mentions possible zeros, but the executable
materializer and active setup filler use minus one; no zero-padding premise is
introduced.

[The active row model](Airbender/Review/Helpers/Tables/NativeDecoderData.lean)
retains each of the three actual decoder prefixes and all 15,728,639 additional
active rows. The final c0-normalization row is excluded. [Symbolic certificates](Airbender/Proofs/Tables/NativeDecoder.lean)
prove the actual sentinel is already present in every prefix, so [full active
membership](Airbender/Review/Helpers/Tables/NativeDecoder.lean) adds no query.
This equivalence is proved from literal data, never supplied as a premise. Physical
lookup multiplicities remain a separate boundary.
Compiled arithmetic/word-memory placement at columns 2/6, native capacity,
supported post-hole rows and both active padding boundaries are checked without
enumerating or allocating a 2^24-row trace.

[The short arithmetic execution bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean)
uses this complete active decoder domain with the existing public constructor,
accepted native matching and sparse execution. The initialized alias regression
still derives PC 24 to 28 and x1=246 through actual exported membership. An
internal word-memory adapter also derives its sparse decoder membership.
Existing native packed-mask/store-mask equations reject the retained sentinel.
These are native data certificates and a source-shaped active-row model; general
Rust full-trace/normalization/LDE refinement, arbitrary-program certificates and
physical lookup/cryptographic enforcement remain separate. No defect is established.

## Complete active setup rows

[Complete row definitions](Airbender/Review/Helpers/Tables/NativeRowsData.lean)
now combine actual scalar prefixes, tagged generic tables and actual decoder
prefixes/fillers at the imported 12/16-column layouts. [Three short claims](Airbender/Review/Helpers/Tables/NativeRows.lean)
recover scalar bounds, actual decoder data and tagged membership. [Projection
proofs](Airbender/Proofs/Tables/NativeRows.lean) also connect these columns to the
unchanged Clean scalar, ROM and separator tables. Full query widths must fit;
the arithmetic layout cannot authenticate a nonexistent generic group.

[Boundary regressions](Tests/NativeRows.lean) check that decoder filler overlaps
the still-active tagged ROM region, while final active rows mix scalar/generic
zeros with decoder minus-one values. Truncated windows, scalar overflow and wrong
padding tags reject. Only small row widths are evaluated; the active domain stays
symbolic. [The short arithmetic bridge](Airbender/Review/Trace/Families/AddSub/PhysicalSetup.lean)
uses actual decoder columns of these complete rows, and the unchanged initialized
alias witness still derives PC 28/x1=246. Native equations, state/memory matching
and public byte/Sail construction retain their existing meanings.

This checks complete source-shaped row assembly and logical column membership.
The decoder connection still covers the three pinned concrete exports. General
Rust trace construction, arbitrary-program decoder certificates, reserved-row
normalization/LDE, physical lookup multiplicities and cryptographic enforcement
remain separate. No implementation defect or table-equivalence premise is added.

## Native jump/branch/SLT fixed effects

[The native control artifact](Airbender/Review/Circuits/JumpBranchSlt/Artifact.lean)
now imports all 33 quadratic/three linear equations, six scalar/eight timestamp
queries and both native fixed triples. Exact port/clock/decoder/setup metadata is
checked. The explicit control profile rejects mixed/repeated/reversed tables and
wrong offsets; memory imports retain their existing meaning.

[Actual native table data](artifacts/setup/jump-control-native.json) comes from
the family table driver and unchanged lossless codec. It retains 65,536 cleanup
rows tagged 17 followed by 128 conditional rows tagged 43, with no inserted dummy
row. The conditional query keeps flags and funct3 in separate columns. [Certificates](Airbender/Proofs/JumpBranchSlt/ControlTables.lean)
prove every cleanup row symbolically, every conditional row by small finite
kernel checks and exact native tagged membership through [two short claims](Airbender/Review/Helpers/Tables/Control.lean).

[The short local circuit claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
derives key bounds, the control result, retained bit one and the cleaned low PC
from actual imported queries. [A full active JAL witness](Tests/JumpControl.lean)
satisfies every equation/lookup and exercises that public claim. Altered results,
oversized flags and a JAL target with bit one set reject; its cleanup-table row
alone remains valid. Three wrong import modes and 27 new importer checks pass.

Initialized jump/branch/SLT reads and original Sail execution remain open.
Public control decoding is checked below. The native PC assessment adds no
verifier-closure premise. General Rust/JSON/Lean refinement, physical trace/normalization/LDE and
cryptographic lookup enforcement remain separate.

## Native control PC bounds

[The short native PC claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
derives both actual outgoing limb bounds under supported decoder masks
1/2/4/8/16. [Selector calculations](Airbender/Proofs/JumpBranchSlt/Selectors.lean)
recover one-hot selection from the five native Boolean equations and packed
mask equation. [PC assembly](Airbender/Proofs/JumpBranchSlt/PC.lean) proves that
outgoing high variable 14 equals candidate variable 43, ranged by actual scalar
query index 5; outgoing low variable 13 equals ranged key 42 or cleaned value 48.
No outgoing/terminal range, expected PC or verifier-PC closure is a premise.
Public-byte/decoder membership now derives that supported mask below;
initialized control execution remains separate.

[Local regressions](Tests/JumpPC.lean) check every native constraint for JAL mask
1 and immediate -4 at PC zero, with target limbs 65532/65535 and actual link
write four. Actual public decoder fields are checked below. The field
minus-one high-limb variant passes all 36 polynomials and the other 15 queries,
but fails actual scalar query index 5. Thus this v3 F01 witness shape is rejected
by v2 native constraints. This does not claim general jump/branch/SLT Sail or
terminal-history soundness, nor resolve other families' boundary obligations.

## Public control decoding

[The public projection](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean)
follows the pinned [native decoder](../../cs/src/machine/ops/unrolled/decoder/jump_slt_branch.rs):
five masks, original x0 operations and the separate zero flag.
SLTI/SLTIU use mask 8, branches use mask 16, and JAL retains raw encoding funct3
bits: JAL -4 has tag 7. The pinned original Sail decoder supplies instructions;
no source v3 NOP, discarded-jump mask or JAL tag convention is imported.
The reused sparse constructor reads every actual public word, keeps unsupported
pure words at their original PCs, preserves the complete minus-one tail, and
rejects missing bytes, effectful decoding or insufficient capacity.

[Proof assembly](Airbender/Proofs/JumpBranchSlt/Decoder.lean) first derives packed
mask <=31 from actual native Boolean/mask equations, excluding every sentinel.
Membership then recovers original bytes/decoding and all ten native query fields.
Canonical PC/immediate limbs, incoming alignment, exact x0 flag, raw funct3 and
supported masks follow. [One short public claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
combines this source recovery with outgoing PC bounds; no caller-supplied mask,
word/PC range, expected decoding result or verifier-PC closure is a premise.

[Public-byte regressions](Tests/JumpDecoder.lean) use JAL -4, an interior UNIMP
hole and original SLTIU-to-x0 at PC 8. The complete native JAL row with tag 7
passes the public claim; its earlier local tag-zero variant fails membership.
The noncanonical high-PC variant retains actual public membership and passes
all polynomials, but fails the native range query. Constructor tests retain
signed/unsigned comparisons, both jumps to x0 and all six branch conditions;
missing bytes/capacity and the full hole/tail domain are checked.

Initialized native control history is checked below. Original Sail cell/instruction
execution and terminal matching remain open. Actual native program-prefix export
is certified below for the concrete input; general Rust decoder/setup/trace
refinement and cryptographic enforcement remain separately scoped.

## Actual native control decoder export

[The actual native prefix](artifacts/setup/jump-decoder-native.json) calls the pinned
signed jump/branch/SLT decoder through the existing preprocessor/materializer.
Its 3.7 KiB lossless artifact retains all 1,048,576 ten-column rows: original
JAL -4 with raw funct3 7, UNIMP at PC 4, original SLTIU-to-x0 at PC 8 and the
complete minus-one tail. Fixture and little-endian text modes reproduce identical
output; partial/oversized text rejects before output. Separate strict importer
profiles reject unsigned-only, crossed-family, malformed and noncanonical data.

[Literal public data](Airbender/Review/Circuits/JumpBranchSlt/Tables/NativeSetupData.lean)
reuses the preceding byte fixture without changing its words or original Sail
instructions. [Certificates](Airbender/Proofs/JumpBranchSlt/NativeSetup.lean) reuse
the arithmetic certificate structure: three finite prefix checks and a symbolic
full-tail proof establish every exported row equals the independently constructed
public table. [One short export claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
then derives public source evidence and outgoing PC bounds from actual membership
and every accepted native constraint, without table-equivalence or range premises.
[Regressions](Tests/NativeJumpSetup.lean) include the full native JAL row, retained
post-hole x0 fields, actual public text and rejection of the old local tag-zero query.

This certifies the concrete input. Arbitrary programs, general Rust/JSON/compiler
refinement, physical trace/normalization/LDE, original Sail control cell/instruction
execution, terminal matching and cryptographic enforcement remain open.
Initialized native control history is checked below.

## Initialized native control history

[The separate control registry](Airbender/Review/Helpers/Context/JumpBranchSlt.lean)
binds all three imported register ports, raw state/clock columns and ten-column
decoder placement. [Native clock extraction](Airbender/Proofs/JumpBranchSlt/Timestamp.lean)
reuses the word-memory calculation structure with the checked control equation/
query indices. Four-tick advancement, 19-bit carry and strict previous-write/port
ordering feed the unchanged shared clock/history proofs through a proved instance.

[One short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean)
uses actual Sail seed/PC construction and full native state/memory matching to
construct complete Clean history and newest preceding reads for every port.
All row/prior clock bounds and seed-address uniqueness are derived. No expected
read, per-row range/clock/order or desired terminal value is supplied.

[The nonempty JAL -4 regression](Tests/ControlHistory.lean) retains both aliased
x0 reads, the public old x1 value 123 and actual link write four. Its second read
consumes the first timestamp refresh; stale local rows still pass every native
constraint but fail full matching. Actual exported decoder membership is retained.
Missing explicit register data rejects initialization. A separate full native row
checks lower-clock carry; derived port effects and terminal clocks are checked.

Control word/write bounds, hardwired-x0 preservation and actual Sail cell history
are now checked below. Original control instruction execution, exact terminal
instruction-state matching, physical control boot, general Rust/trace refinement
and cryptographic enforcement remain separate.

## Initialized control values and Sail cells

[Native write calculations](Airbender/Proofs/JumpBranchSlt/Writes.lean) derive the
actual destination bounds from the one-hot native selectors, masked-write
equations, scalar-ranged link and exact conditional-control table. Successful
public sparse decoding supplies supported masks and the x0 flag. [The short
range claim](Airbender/Review/Trace/Families/JumpBranchSlt/Values.lean) combines
these rules with public seeds and unchanged decreasing-time history induction,
deriving every native read/write/terminal word bound, including aliased refreshes.

[Native x0 preservation](Airbender/Proofs/Trace/Families/JumpBranchSlt/ZeroRegister.lean)
uses the actual destination address, decoded zero flag and four native write
equations. Shared induction derives zero-valued x0 writes throughout the accepted
history. [The short Sail cell claim](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean)
reuses unchanged row grouping and Clean-to-Sail realization to derive intermediate
states and actual cell reads/writes in native clock order. It supplies no expected
read, per-row bound, selected schedule or intermediate state.

[The exported-JAL regression](Tests/ControlValues.lean) constructs the same public
bytes with the explicit initialized register state, transfers actual exported
membership and applies both claims. It retains both x0 refreshes and checks that
the actual final port reads old x1=123 and writes the link four. A malformed
zero flag of two satisfies all local native constraints and makes the write
unbounded; full decoder membership rejects it. This checks the explicit lookup
boundary rather than establishing an accepted-trace defect. Original control
instruction execution, terminal instruction-state matching, physical control
boot and Rust/compiler/cryptographic refinement remain open.

## Initialized control register transfers

[The native port connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/PortReads.lean)
reuses unchanged readonly-prefix transport: both source reads and the old
destination read use one cell-history pre-state, even with aliases. Full native
decoder membership identifies the actual original Sail GPR accessors; the final
port performs the actual masked register write, retaining x0 behavior.

[One public claim](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean)
combines actual public sparse construction with initialized native matching and
[proof-layer segment assembly](Airbender/Proofs/Trace/Families/JumpBranchSlt/RegisterHistory.lean).
Derived clock order fixes the complete row sequence. Shared append/split proofs
construct each row's before/after states and its older/current/newer Sail histories;
no segment state, expected read, selected schedule or desired write is supplied.
Each segment retains source evidence from original public bytes and pure Sail decoding.

[The exported-JAL regression](Tests/ControlRegisters.lean) extracts its singleton
segment from that public theorem and derives both x0 reads, old x1=123 and the
actual link write four. This connects original register accesses to native cell
transfers; original control instruction clauses, native branch/jump/comparison
semantics, PC preparation/retirement and full terminal instruction-state matching
remain open. Physical setup/Rust/compiler/cryptographic refinement stays separate.

## Native saved jump links

[Native link arithmetic](Airbender/Proofs/JumpBranchSlt/Link.lean) now reuses the
original Boolean carry extraction and unchanged modular word addition. Actual
v2 assertions 9/5 constrain low/high carries 49/28; equations 29/30 compute the
saved PC+4 in scalar-ranged columns 26/27. Native equations 20..23 then force the
actual destination columns 38/39 to that word or the discarded x0 write.

[One short circuit claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean)
uses actual public sparse construction and full native decoder membership to
derive both PC bounds and the exact zero flag. Masks one/two classify the native
JAL/JALR domain; [packed-mask recovery](Airbender/Proofs/JumpBranchSlt/Selectors.lean)
derives every operation selector. No selector, carry, PC-word bound, flag or
expected write is supplied. The original v3 field inverse is not reused.

[Regressions](Tests/JumpLink.lean) retain the actually exported negative JAL link,
check all native constraints for an odd-source JALR and original JAL-to-x0, and
construct their independent original-byte logical setup. The JALR link is eight;
the x0 row retains raw link twelve but writes zero. An unmasked x1 link wraps
from PC 0xfffffffc to zero under all native constraints; that case is a local
row regression, not an initialized/public-decoder trace. Altered link data fails.
General native export certificates for the new logical fixture,
comparison/branch semantics, original Sail clauses/PC retirement and full terminal
instruction-state matching remain open. Rust/compiler/cryptographic refinement
stays separate.

## Initialized native jump targets

[Native target calculation](Airbender/Proofs/JumpBranchSlt/Target.lean) now reuses
original modular word addition and bit cleanup with v2 bindings. Assertions 10/8
constrain carries 50/44; equations 31/32 add PC or rs1 and the immediate into
candidate 42/43. The actual sixth scalar query bounds the high candidate, so no
v3 final-high closure premise is imported. Native cleanup query 15, alignment
assertion 26 and routing equations 27/28 derive the final PC and four-byte alignment.
JAL preserves its even sum; JALR clears bit zero and rejects a sum with bit one set.

[The short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean)
uses public Sail initialization, complete native matching and full sparse decoder
membership. Shared initialized induction derives source bounds; actual public
bytes supply PC/immediate ranges and exact mask identity. The unchanged original
[Sail decoder parity proof](Airbender/Proofs/Sail/Decoder.lean) and native metadata
projection derive JAL offset parity. No operand bound, selector, parity, carry,
expected read or desired target is supplied by the public caller.

[Regressions](Tests/JumpTarget.lean) derive the actually exported negative-JAL
target 0xfffffffc from public PC zero. A new logical original-byte JALR fixture
starts at PC four with public x1=257; native matching retains the aliased rs1/rd
refresh and derives target 264 from odd sum 265. Its full public initialization,
lookup and every native equation/query are checked. Local JAL-to-x0 and modular
0xfffffffc-plus-eight target regressions pass. A bit-one JALR target has a valid
cleanup row but is rejected by native alignment. Local wrap is not an initialized
execution certificate, and the new logical fixture has no new general native
export certificate. Original Sail instruction clauses/PC retirement, branch
semantics, complete control execution and terminal instruction-state
matching remain open; Rust/compiler/cryptographic refinement stays separate.

## Initialized native comparison results

[Native comparison calculations](Airbender/Proofs/JumpBranchSlt/Comparison.lean)
now derive the actual masked SLT/SLTU/SLTI/SLTIU result. Equations 29/30 and
Boolean carries 49/28 reuse original subtraction/borrow lifting and unchanged
word arithmetic. Actual scalar queries zero/one range remainder 26/27. Assertions
18/19 use positive high-limb flags 31/33 and scalar-ranged shifted limbs 32/34;
the proof keeps this native encoding and complements the flags in the actual
four-bit control key. Inverse equations 16/17 derive equality-bit Booleanity.
The checked native conditional table determines signed/unsigned result 35, and
write equations 20..23 force actual masked destination 38/39.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean)
uses actual public bytes, full sparse decoder membership and complete native
matching. Native packed masks derive register/immediate selectors; original
metadata derives signed/unsigned funct3 and the x0 flag. Shared initialized range
induction supplies both register words, while public decoding bounds the immediate.
No selector, sign/borrow bit, operand bound, expected read or desired result is
supplied. The original [signed word-ordering lemmas](Airbender/Proofs/Arithmetic/Comparison.lean)
are copied unchanged, with source hashes recorded.

[Four separately initialized regressions](Tests/ControlComparisons.lean) compare
register -1 with one (SLT true, SLTU false), and positive source 123 with the
sign-extended immediate -1 (SLTI false, SLTIU true). The original SLTIU-to-x0
retains raw result one but writes zero, with its rd read consuming the dummy x0
readonly refresh. That query also occurs in the prior actual native export.
All original-byte construction, public register/PC initialization, native
constraints and memory matching are checked. A reversed positive flag preserves
its high-limb field equation with shifted value 98303, but actual scalar query two
rejects it. This is enforcement of the native range boundary, not a new defect.
The new logical program has no new general native export certificate. Branch
semantics, original Sail instruction clauses/PC retirement, complete control
execution and terminal instruction-state matching remain open; general
Rust/compiler/cryptographic refinement stays separate.

## Native comparison PC advancement

[Comparison PC arithmetic](Airbender/Proofs/JumpBranchSlt/ComparisonPC.lean)
now derives PC+4 and four-byte alignment for SLT/SLTU/SLTI/SLTIU, including
RV32 rollover. Native equations 24/25 exclude branch routing; equations 31/32
and Boolean carry assertions 10/8 determine candidate 42/43. Actual scalar
queries four/five bound both limbs. Equations 27/28 route that raw candidate
directly to final PC 13/14. Unlike the source layout, comparison PC does not
pass through cleanup. Original modular word addition is reused unchanged;
no final-high closure assumption is imported.

[One short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean)
derives incoming PC bounds/alignment and comparison identity from original
public bytes, complete decoder membership and native acceptance. It needs no
register-image boundary: this numerical PC calculation reads no source GPR.
No per-row selector, carry, range, alignment or expected PC is supplied.
[Regressions](Tests/ComparisonPC.lean) reuse all four separately initialized
comparison fixtures, check a full native local 0xfffffffc-to-zero row, and reject
an altered outgoing PC with unchanged decoder columns. The wrap row is local,
not an initialized/public-decoder execution or a new native program export.
Original Sail instruction clauses/retirement, branch semantics and complete
control execution/terminal instruction-state matching remain open. General
Rust/compiler/cryptographic refinement remains separate. No new v2 defect is
established.

## Initialized native branch conditions

[Native branch calculations](Airbender/Proofs/JumpBranchSlt/Branch.lean) now
derive BEQ/BNE/BLT/BGE/BLTU/BGEU conditions from actual constraints. Original
word subtraction/borrow and signed ordering are reused unchanged. Scalar
queries zero/one range remainder 26/27; inverse equations 16/17 identify equality
bit 29 with equality of both operand words. The unchanged positive-high proof
is shared with comparisons, preserving native flags 31/33 and scalar queries
two/three. The actual conditional table determines result 35; equations 24/25
derive taken/complement 46/45. Equations 20..23 force the actual unused write
38/39 to zero independently of the decoder-owned x0 flag.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean)
derives both operand bounds from complete native matching and branch identity
and all six funct3 tags from original public bytes/decoding. No per-row range,
selector, equality/sign/borrow bit, expected read or desired condition is supplied.
[Eighteen initialized regressions](Tests/Branches.lean) use the six original
branch words and operand pairs (-1,1), (1,-1) and (1,1). Every opcode has both
outcomes; signed/unsigned disagreement, equality, complementary routing and
the retained zero destination event are checked through full native acceptance,
public initialization and decoder membership. A false equality flag and false
BEQ answer satisfy the actual conditional table but fail the native inverse
equation. This confirms enforcement, not a new v2 defect. The new logical program
has no new native export certificate. Branch target arithmetic, original Sail
clauses/retirement and complete control execution/terminal instruction-state
matching remain open; general Rust/compiler/cryptographic refinement is separate.

## Initialized native branch targets

[Native branch PC arithmetic](Airbender/Proofs/JumpBranchSlt/BranchPC.lean)
now derives PC+offset when taken and PC+4 otherwise, preserving RV32 wrap and
four-byte alignment. Equations 24/25 derive complementary routing; equations
31/32 and the unchanged native Boolean-carry proof determine candidate 42/43.
Actual scalar queries four/five bound both limbs. An untaken row routes the raw
candidate; a taken row uses cleanup, but original offset parity and native
assertion 26 exclude either low target bit before cleanup. Both cases therefore
retain the exact calculated word. Original modular word addition is reused
unchanged; no final-high closure premise is imported.

[One short initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean)
reuses the checked six branch conditions from initialized matching. Original
public decoding derives incoming PC/offset bounds, alignment, exact selectors
and offset parity through the unchanged Sail decoder/sign-extension lemmas.
No per-row bound, parity, carry, decision or desired PC is supplied.
[Regressions](Tests/BranchTargets.lean) reuse all eighteen initialized original
branch cases. Full local native rows additionally cover taken offset -4, taken
PC+8 wrap and untaken PC+4 wrap with ignored offset two. A taken offset-two row
has valid cleanup membership but fails the actual bit-one assertion. The local
negative/wrap rows are not initialized/public-decoder executions or new native
program exports. No v2 defect is established. Original Sail clauses/retirement,
complete control execution and terminal instruction-state matching remain open;
general Rust/compiler/cryptographic refinement stays separate.

## Initialized original comparison clauses and retirement

[Original comparison execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
now connects SLT/SLTU/SLTI/SLTIU to their pinned original Sail clauses and normal
preparation/retirement. The native result proof and initialized matching derive
both operands, signed/unsigned comparison and the actual masked write. Public
decoder columns recover exact constructors, indices, immediate sign extension
and distinct register/immediate masks. Original word-ordering, register access,
PC preparation, history framing and retirement lemmas are reused unchanged.
The source nonzero-destination and final-high interfaces are not imported:
native v2 x0 operations retain their original reads, and actual candidate range
queries already supply both successor bounds.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean)
constructs the complete clock-ordered native cell history and every comparison's
before/after states. The original clause retires to the exact native output PC
in those derived states; no operand, result, prepared state, successor or
intermediate state is supplied. [Regressions](Tests/ComparisonExecution.lean)
reuse all four separately initialized original-byte fixtures and execute from
their actual public states. SLTIU-to-x0 reads public x1=123, discards its true
comparison against sign-extended -1, preserves the complete data state and
retires PC eight to twelve. This is a segment execution/retirement result;
general fetched trace composition and terminal instruction-state matching,
original jump/branch clauses and their CSR effects remain separate. New native
program export, general Rust/compiler and cryptographic refinement are not
claimed. No v2 implementation defect is established.

## Initialized original branch clauses and retirement

[Original branch execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/BranchExecution.lean)
now connects all six native branch conditions and targets to pinned original
Sail BTYPE clauses and normal preparation/retirement. Complete native matching
derives both source bounds and actual same-pre-state reads; original public
decoding derives the BTYPE constructor, indices, funct3 and sign-extended offset.
The existing native target proof supplies exact PC+offset/PC+4 and four-byte
alignment, including the previously checked RV32 arithmetic wrap behavior.
The source branch mask twenty-four and old columns/final-high interface are
replaced by native v2 mask sixteen, actual ports and derived target bounds.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean)
constructs every before/after state and retires the original clause to the native
output PC. Original Sail requires a successful misa read on a taken aligned
target. A real public initial CSR entry is therefore explicit; its value is
unrestricted. The [original control-flow module](Airbender/Proofs/Sail/ControlFlow.lean)
is copied unchanged, and [unchanged CSR frame proofs](Airbender/Proofs/Trace/ControlFlowCSR.lean)
transport that entry through complete native history. No per-row CSR, operand,
result, prepared state, target PC, final-high closure or intermediate state is
supplied.

[Regressions](Tests/BranchExecution.lean) reuse all eighteen native original-byte
fixtures unchanged and add only the actual public misa entry, universally over
its 32-bit value. Both outcomes of every opcode execute from their actual public
states, derive complete data-state stuttering from the real discarded write and
reach the checked target. The prior partial fixtures have no misa entry and the
original accessor cannot succeed there. This is an explicit original-state
boundary, not a native constraint defect; a whole missing-CSR branch exception
trace is not claimed. General fetched control composition/terminal instruction-
state matching, original JAL/JALR clauses and their landing-pad CSR profile,
new native program exports and general Rust/compiler/cryptographic refinement
remain separate.

## Initialized original jump clauses and retirement

[Original jump execution](Airbender/Proofs/Trace/Families/JumpBranchSlt/JumpExecution.lean)
now connects checked native JAL/JALR links and aligned targets to pinned original
clauses and preparation/retirement. [Pure jump definitions](Airbender/Proofs/JumpBranchSlt/JumpModel.lean)
and the complete [original retirement declaration](Airbender/Proofs/Sail/JumpRetirement.lean)
are copied unchanged into internal modules. Native v2 masks one/two, immediate
9/10, actual masked destination 38/39 and PC 13/14 replace the source layout.
JAL's original raw funct3 bits and x0 masking remain intact. Existing native
queries and matching derive ranges/targets, including RV32 wrap, without the
source final-high closure premise or supplied link/read/result/state.

[The public segment claim](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean)
constructs every history segment and executes its exact public-decoded clause.
A real initial misa entry has unrestricted value. Traces containing JALR use
actual initial Machine privilege and a real mseccfg value with MLPE clear;
other security bits are unrestricted. Unchanged CSR frames derive those reads
at every row. JAL-only traces need no privilege/security entries. Original
landing-pad behavior is retained under this explicit platform profile.

[Regressions](Tests/JumpExecution.lean) reuse the unchanged exported negative-JAL
and logical aliasing-JALR native histories, bytes and decoder certificates,
adding only actual public CSR entries. JAL retires PC zero to 0xfffffffc and
writes link four over x1=123. JALR reads old x1=257 before its aliased link write
eight and retires PC four to 264, clearing bit zero of 265. Both original
retirements share the exact native write's constructed after-state. The JAL
state has no privilege/security entry; the prior partial JALR state's original
privilege accessor cannot succeed. No native defect or whole missing-CSR
exception trace is claimed. Full fetched control composition and terminal
instruction-state matching, new native program exports and general
Rust/compiler/cryptographic refinement remain separate.

## Fetched control execution and terminal matching

[The complete control claim](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean)
now composes JAL/JALR, all six branches and SLT/SLTU/SLTI/SLTIU into finite
original Sail execution from public initialization. The unchanged shared
composer derives actual row order, intermediate states, fetch/decode evidence
and every preparation/execution/retirement step. Native register history
preserves the public instruction bytes. Existing native retirement proofs
supply each row's behavior; actual terminal PC and tracked register reads
follow from full state/memory matching. Scalar candidate queries and state
matching also derive both raw terminal PC limb bounds, including empty traces;
no source terminal-closure premise is copied.

The actual initial misa entry and conditional JALR Machine/MLPE-clear profile
remain explicit; history transports their reads. No schedule, intermediate
state, expected read/result, per-row step or terminal bound is supplied.
[Existing jump/branch fixtures and an empty trace](Tests/ControlExecution.lean)
check fetched execution, including negative JAL and all eighteen branch cases.
[A two-row logical native program](Tests/ControlSequence.lean) presents JAL then
aliasing JALR in reverse witness order: JAL writes x1=4, JALR consumes that link
and writes x1=8, and the composed execution ends at PC four. A stale x1=124
variant still passes every local native constraint, public decoder membership
and full state matching, but actual memory matching rejects it. This is a
checked enforcement boundary, not a native defect or a new Rust program-export
certificate. Unified whole-machine/protocol composition, remaining families,
physical initialization/teardown and general Rust/compiler/cryptographic
refinement remain separate.

## Unsigned mul/div native artifact and byte tables

[The native artifact](Airbender/Review/Circuits/MulDiv/Artifact.lean) now retains
all 43 quadratic/six linear equations, six scalar/eight timestamp queries and
six exact three-column RangeCheckSmall queries. These pair all eleven declared
byte columns; the final odd column keeps two zero padding entries. Checked
native setup metadata retains table ID eight, offset zero and 65,536 rows.
Native state/port/decoder metadata is imported separately from semantic claims.
Two optimized-out variables retain bounded, unique scratch metadata; every
attempt to consume such an address as a constraint/query input is rejected.

[Actual native table-driver data](Airbender/Review/Helpers/Tables/NativeSmallRangeData.lean)
is exported reproducibly from pinned v2 Rust with its fourth tag column.
[Symbolic certificates](Airbender/Proofs/MulDiv/SmallRange.lean) prove every one
of the 65,536 actual rows and exact Clean membership through stored periodic
columns, without enumerating the domain or assuming table equivalence.
[The native queries](Airbender/Proofs/MulDiv/ByteBounds.lean) derive all eleven
byte bounds directly from accepted local constraints. No numerical bound or
expected arithmetic result is supplied.

[Boundary regressions](Tests/MulDivArtifact.lean) accept byte endpoints and
reject overflow, nonzero third padding and wrong native tags. Importer
mutations reject missing/repeated/unmapped queries, odd-byte padding changes,
optimized-out equation/query use, scratch overflow/aliasing and altered table
profiles/geometry. This closes the unsigned mul/div importer dependency;
At this artifact checkpoint numerical correctness, public decoding, initialized
history and original Sail execution were still unfinished. The numerical
connection is checked below. No native defect is established.
General Rust/compiler/physical argument refinement remains separate.

## Native unsigned MUL/MULHU/DIVU/REMU arithmetic

[The public numerical claim](Airbender/Review/Circuits/MulDiv/Theorems.lean)
now derives both the selected result and actual destination-zero-masked write
from all accepted native equations/queries. Its explicit local interfaces are
the native packed operation mask, the input register's two-limb bound and the
actual destination-zero flag. No quotient, remainder, product, byte/carry/output
range or desired result is supplied. Public decoding, initialized history and
original Sail preparation/execution/retirement remain subsequent connections.

[The product connection](Airbender/Proofs/MulDiv/Product.lean) reuses the entire
unchanged shared integer byte-column theorem. V2 explicit bytes and split
carries replace source aliases; native queries/assertions derive every needed
byte/carry/output bound. [Division](Airbender/Proofs/MulDiv/Division.lean)
rebinds the inverse scale to 32768 in Mersenne31, derives a strict nonzero
remainder bound from the native borrow and resolves zero divisors to quotient
0xffffffff and remainder equal to the dividend. [Result assembly](Airbender/Proofs/MulDiv/Results.lean)
binds native packed masks MUL=2, MULHU=0, DIVU=3, REMU=1, raw result selection
and both actual masked write limbs. Calculations stay under Proofs.

[Forty full local native witnesses](Tests/MulDivWitness.lean) cover all four
operations, both ordinary/discarded x0 writes, zero/zero, maximal dividend with
zero divisor, maximal product, divisor 257 and 123 divided by seven. Each of
[the four](Tests/MulDivMul.lean) [operation](Tests/MulDivMulhu.lean)
[modules](Tests/MulDivDivu.lean) [checks](Tests/MulDivRemu.lean) proves every
native equation/query, applies the public claim and rejects a corrupted actual
write. Proofs are split at the default proof-step limit; memory/thread ceilings
are unchanged. These are complete local assignments, not initialized fetched
execution or new native Rust program exports. No v2 defect is established.

## Initialized unsigned MUL/DIV decoding and native results

[The short public trace claim](Airbender/Review/Trace/Families/MulDiv/Theorems.lean)
now derives all local numerical interfaces from actual public bytes, seed/PC reads
and accepted native state/memory/decoder matching. MUL/MULHU/DIVU/REMU selected
results and actual masked destination writes follow, including zero divisors and
original x0 destinations. No per-row operand bound, packed selector, zero flag,
expected read or desired result is supplied. Original Sail operation clauses,
preparation/retirement and finite fetched MUL/DIV execution remain unfinished.

[Stateful sparse construction](Airbender/Review/Helpers/Decoder/StatefulSetup.lean)
executes the pinned original Sail decoder in the public initial state. It retains
native PCs 4*i, unsupported instruction holes, capacity and the complete
all-minus-one tail. Byte/decoder errors reject construction. Extension-dependent
decoding reads actual misa; the earlier pure constructors remain available for
their checked base-ISA families. [The entire decoder-frame proof](Airbender/Proofs/Sail/DecoderFrame.lean)
is copied unchanged from the pinned source and proves state preservation and
replay with the same misa. Native two-bit mask equations exclude all sentinel
slots before membership recovers original source evidence and exact query data.

[Initialized native history](Airbender/Review/Trace/Families/MulDiv/History.lean)
reuses complete Clean online consistency and latest-read assembly for all three
native ports. Checked native clock equations discharge the shared instance.
[Range induction](Airbender/Review/Trace/Families/MulDiv/Values.lean) retains both
readonly timestamp refreshes and the actual masked destination write, deriving
every native read, write and terminal word bound. [Numerical assembly](Airbender/Proofs/Trace/Families/MulDiv/Results.lean)
then invokes the previously checked native arithmetic with these derived inputs.

[Sixteen complete initialized traces](Tests/MulDivInitializedFixture.lean) cover
all four operations, ordinary/x0 writes and ordinary/zero divisors. Actual public
bytes and misa=0x40001000 construct their native-shaped setup, including an UNIMP
hole and the full 2^20-row tail. [Original-decoder regressions](Tests/MulDivDecoderCases.lean)
reject every opcode when M is disabled. [Boundary regressions](Tests/MulDivMetadata.lean)
retain locally valid wrong tags and a compensating flag-2/unbounded write, then
prove full public lookup membership rejects both. These are logical argument
boundary checks, not native defects or new Rust program-export certificates.
Physical initialization, setup/compiler refinement, cryptographic enforcement,
whole-machine/protocol composition and completeness remain separately scoped.

## Original Sail MUL/DIV register histories

[The short public register-history theorem](Airbender/Review/Trace/Families/MulDiv/Registers.lean)
now derives original Sail operand/old-destination reads and the actual masked
write from public bytes, initialized seeds and accepted native matching. All
three reads use the same instruction pre-state, including source/destination
aliases. Clock-derived ordering and every segment state are constructed.
[Observable definitions](Airbender/Review/Helpers/Memory/MulDiv.lean) keep the
public statement short; calculations and proof assembly stay under Proofs.

[Native x0 preservation](Airbender/Proofs/Trace/Families/MulDiv/ZeroRegister.lean)
uses actual write equations 35/36 and decoder-owned flags, then invokes unchanged
shared Clean-to-Sail realization. The original generic three-port address/read/
write declarations are copied unchanged from the pinned source and resolve
against checked native v2 metadata. [Code/configuration frames](Airbender/Proofs/Trace/Families/MulDiv/CodeHistory.lean)
preserve every public byte and misa, replaying original stateful decoding in
real later states without a per-row decoding or CSR-read premise.

[All sixteen initialized cases](Tests/MulDivRegisters.lean) now obtain actual
Sail writes and full-state stuttering for x0. [A reversed two-row program](Tests/MulDivRegisterChain.lean)
checks MUL x3,x1,x2 followed by MUL x1,x1,x2, with actual original bytes at PCs
zero/four and a real first update. The second decoder runs in its constructed
pre-state; aliased operand/destination reads are 123/7 and the actual write is
861. The stale old-destination timestamp retains all local constraints, public
decoding and state matching but fails native memory matching. This validates
the logical argument boundary, not a native defect or a new Rust export.

Original MUL/DIV operation clauses, preparation/PC retirement and finite fetched
execution remain unfinished. These are Sail cell-transfer histories, not full
instruction traces. Physical boot/setup/compiler refinement, cryptographic
argument enforcement, unified execution/protocol spans and completeness remain
separately scoped.

## Original local MUL/DIV execution and PC retirement

[The short public instruction-history theorem](Airbender/Review/Trace/Families/MulDiv/Execution.lean)
now combines constructed real register histories with original local MUL,
MULHU, DIVU and REMU execution. [Its observable definitions](Airbender/Review/Helpers/Memory/MulDivExecution.lean)
record original instruction identity, actual native successor bounds and the
original preparation/clause/retirement transition for every native row. Public
bytes, initialized matching and decoder membership derive the operand ranges,
register reads, operation selection, x0 behavior and PC inputs.

[Original clause assembly](Airbender/Proofs/MulDiv/Clauses.lean) reuses the pinned
source's signed low-product, unsigned high-product and integer division/remainder
proofs against actual native v2 results and masked writes. [Local retirement](Airbender/Proofs/MulDiv/Execution.lean)
transports real native cell histories through Sail's own nextPC preparation and
PC retirement, identifying the complete actual after-state. Original discarded
x0 operations and source/destination aliases are retained.

[The native PC proof](Airbender/Proofs/MulDiv/PC.lean) checks actual Boolean,
carry and inverse gates, deriving both successor bounds and modular RV32 PC+4.
[A full imported native row](Tests/MulDivPC.lean) satisfies every equation and
lookup while wrapping 0xfffffffc to zero. [All sixteen initialized cases](Tests/MulDivExecution.lean)
execute the original four clauses, including zero divisors and x0 writes that
still retire PC. [The actual alias sequence](Tests/MulDivRegisterChain.lean) now
executes and retires the second original MUL from PC four to eight after its
real prefix update.

These are original local instruction transitions over constructed histories.
Complete finite fetched MUL/DIV execution still needs stateful-decoder-aware
composition; no fetched wraparound program or new Rust export is claimed.
Physical initialization, general Rust/JSON/compiler refinement, cryptographic
argument enforcement, unified execution/protocol spans and completeness remain
separately scoped. No native defect is established by this checkpoint.

## Complete fetched MUL/DIV execution

[The short public fetched-execution theorem](Airbender/Review/Trace/Families/MulDiv/FetchedExecution.lean)
now derives a finite original Sail execution from actual public initialization
to the native terminal PC and register values. Every step fetches public bytes,
runs original stateful decoding in its real pre-state, and uses original MUL,
MULHU, DIVU or REMU preparation/execution/retirement. Actual native equations,
full decoder membership and initialized matching derive all operand reads,
ranges, masks, row order, intermediate states and PC boundaries. Terminal PC
bounds come from native successors or the public initial PC for an empty trace.

[Stateful composition](Airbender/Proofs/Trace/StatefulComposition.lean) adapts the
existing native row induction and reuses the unchanged original decoder-frame
proof. It derives replay through PC bookkeeping from actual misa preservation;
the public claim has no pure-decoder, separate ISA-read, replay or per-row step premise.
[Family assembly](Airbender/Proofs/Trace/Families/MulDiv/Composition.lean) reuses
actual code/configuration frames, native clocks, real history splitting and the
unchanged shared terminal-state/read proof. The prior pure composition helper
and original Sail/Clean semantics remain unchanged.

[Complete regressions](Tests/MulDivFetched.lean) cover all sixteen initialized
cases, concrete terminal arithmetic values, original x0 discards, unsigned
zero-divisor behavior and empty execution. The actual newest-first two-MUL
alias program now fetches/decodes after a real prefix update and reaches PC
eight with x1 and x3 equal to 861, without supplied intermediate or final-state
premises. The previous stale-timestamp negative test remains rejected by native
memory matching.

The local native PC proof retains aligned RV32 rollover; this checkpoint adds
no fetched wraparound fixture or new Rust export. Physical initialization,
general Rust/JSON/compiler refinement, cryptographic argument enforcement,
unified execution/protocol spans and completeness remain separately scoped.
Shift/binop and subword memory are next. No native defect is established.

## Actual native shift/binop decoder data

[The short public data certificate](Airbender/Review/Trace/Families/ShiftBinop/NativeDecoder.lean)
connects actual Rust preprocessing/materialization to independently read public
bytes and original Sail decoding for twelve ordinary register/immediate forms,
their twelve original x0 variants and an unsupported ADD hole. Every one of the
1,048,576 exported rows is checked. [Internal proofs](Airbender/Proofs/ShiftBinop/NativeSetup.lean)
check the small prefix and actual stored sentinel blocks structurally, reusing
existing sparse setup and column proof structure with no table-equality premise.

The native v2 profile retains x0 destinations, uses full sign-extended 16-bit
binary immediate limbs, and retains SRAI funct7 bits (shift 31 gives immediate
1055). Its operation mask/tag encoding differs from v3. [Regressions](Tests/ShiftDecoder.lean)
check those differences and unsupported constructors. Actual exporter runs
reproduce both fixture and binary-text output, reject unsupported REV8/rotate
and illegal RV32 shift words, and confirm filtering with an empty CSR allow-list.
Strict import profiles reject malformed data and crossed arithmetic/control exports.

This is a finite native decoder-data certificate. Dynamic lookup selectors and
the large shift/binop tables still require a checked constraint import; the
compiled importer continues rejecting them. Shift/binop circuit soundness,
initialized execution, custom CSR/oracle semantics, general Rust/compiler
refinement and cryptographic enforcement remain separate. No native defect is
established. The next checkpoint is native dynamic table import and membership.

## Native zero and binary lookup rows

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeBinary.lean)
now identify original Clean XOR/OR/AND membership with actual native tagged rows
and derive both byte-key bounds and the exact bytewise result. The actual Rust
driver exports the complete low-ID prefix: zero plus tables 4/6/7 at offsets
0/1/65537/131073. Reproduction checks those offsets against the native compiled
layout. All 196,608 binary rows and the conditional zero row are certified.

[Output certificates](Airbender/Proofs/Tables/BinaryXorCertificate.lean) reuse
the source's full literal-block kernel-check structure; OR and AND have matching
certificates. [Geometry](Airbender/Proofs/Tables/BinaryColumns.lean) proves actual
periodic keys, tags and block coverage structurally. [Internal assembly](Airbender/Proofs/Tables/Binary.lean)
connects these to exact native membership and bitwise results without supplied
bounds, output values or table-equivalence premises. Two generic source proof
modules and the mathematical byte-operation definition are copied unchanged.

[Regressions](Tests/NativeBinary.lean) retain native offsets/zero data, cover
complementary and terminal byte keys and reject byte 256 or a changed XOR result.
Strict import profiles reject malformed prefix data and crossed control/mul-div
artifacts. The combined geometry check initially hit Lean's allocation cap;
splitting it and replacing evaluated coverage with source-shaped structural
geometry resolved it under the unchanged caps.

This closes the native binary-table prerequisite. Dynamic selectors, large
16-bit shift tables, custom CSR/oracle semantics, shift/binop circuit soundness
and initialized execution remain unfinished. General Rust/JSON/compiler and
physical cryptographic enforcement remain separate; no native defect is established.

## Native truncation, padded range and sign-fill rows

[Four short public helper claims](Airbender/Review/Helpers/Tables/NativeShiftScalars.lean)
connect original Clean membership to actual native truncation, sign-fill and
zero-padded range rows. They derive input/limb bounds, low-five-bit truncation,
both zero padding fields and the exact RV32 sign-fill mask. Negative input at
shift zero yields an empty mask, matching the native unbounded shift by 32.

[Actual exported data](artifacts/setup/shift-scalars-native.json) contains all
2,228,224 selected rows, including the complete 2,097,152-row sign-fill table.
Native IDs 47/52/53 retain compiled offsets 200705/8654849/10752001; unexported
regions are not erased from placement metadata. Rust materializes and drops each
selected table separately, verifies its lossless compression and JSON roundtrip,
and reproduction compares the artifact and offsets with the pinned native layout.

[Internal geometry](Airbender/Proofs/Tables/ShiftScalarColumns.lean) reuses the
unchanged affine getters and periodic-column proof. [Lower](Airbender/Proofs/Tables/SignFillLow.lean)
and [upper](Airbender/Proofs/Tables/SignFillHigh.lean) sign-fill proofs select actual
constant blocks over 64 symbolic half-limb domains; they do not enumerate two
million rows. [Independent mask arithmetic](Airbender/Proofs/Tables/ShiftScalarBounds.lean)
and [membership assembly](Airbender/Proofs/Tables/ShiftScalars.lean) supply the
short public claims without output, range or table-equivalence premises.

[Regressions](Tests/NativeShiftScalars.lean) cover truncation/range terminal keys,
negative shifts zero/one/sixteen/31, positive sign boundary and changed results,
nonzero padding and oversized packed keys. The combined upper-mask proof reached the resident ceiling; splitting it into
four independent 16-domain certificates resolved the calculation without raising
resource limits. Strict import rejects crossed profiles,
wrong native tags/offsets, missing or noncanonical columns and incomplete extents.

This closes the native scalar/sign-fill table prerequisite. Four large logical
shift tables and dynamic constraint import remain next, followed by numerical
family soundness and initialized execution. Custom CSR/oracle semantics, general
Rust/JSON/compiler refinement and cryptographic enforcement remain separate.
No native implementation defect is established.

## Native low-input logical right shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSrlLow.lean)
connect original Clean membership to every actual native low-input SRL row.
Membership derives the packed-key/output bounds, zero high output and exact
RV32 logical-right-shift result of the zero-extended 16-bit input limb. No
bounds, output values or table-equivalence premises are supplied.

[The native export](artifacts/setup/shift-srl-low-native.json) retains ID 50,
compiled offset 4460545 and all 2,097,152 rows. The existing regional exporter
now shares its unchanged native-generation/codec pipeline with this profile.
Reproduction checks the entire artifact and actual compiled offset, and retains
byte-identical output for every existing native profile. Strict import rejects
changed tags/offsets, field/profile/version, incomplete or noncanonical columns,
wrong extents and crossed binary/scalar/control/mul-div profiles.

[Actual stored-block partitions](Airbender/Proofs/Tables/SrlLowParts.lean)
retain all 74 blocks and their exact extents. Six source-shaped output
certificates, beginning with [the affine/periodic prefix](Airbender/Proofs/Tables/SrlLowPart0.lean),
prove all block entries symbolically. They reuse unchanged affine and periodic
getters and the original block checker, avoiding two-million-row enumeration.
[Independent arithmetic](Airbender/Proofs/Tables/SrlLowMath.lean) connects division
by powers of two to the standard RV32 bitvector shift; [internal assembly](Airbender/Proofs/Tables/SrlLow.lean)
combines this with actual native keys, padding, tags and complete membership.

[Regressions](Tests/NativeSrlLow.lean) cover shifts zero/one/fifteen/sixteen/31,
the final surviving bit and its lower boundary, the actual final native row,
and malformed output/high-padding/packed-key queries. All certificate modules
use the same serial Lean and sampled watchdog ceilings.

This closes one of the four native logical-shift table connections. The two
left-shift tables and high-input right-shift table remain, followed by faithful
dynamic lookup import, numerical family soundness and initialized execution.
Custom CSR/oracle semantics, general Rust/JSON/compiler refinement and
cryptographic enforcement remain separate. No native defect is established.

## Native high-input logical left shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSllHigh.lean)
connect original Clean membership to all actual native high-input SLL rows.
Membership derives packed-key/output bounds, zero low output and exact wrapped
RV32 logical-left-shift semantics for the input limb placed in bits 16–31.
The whole word is reconstructed as a bitvector from its canonical limb; no
whole-word Mersenne31 cast, output bound or table-equivalence premise is supplied.

[The native export](artifacts/setup/shift-sll-high-native.json) retains ID 49,
compiled offset 2363393 and all 2,097,152 rows. The unchanged selected-table
pipeline obtains values/tags from the native Rust API and placement from the
pinned compiled layout. Reproduction checks the complete artifact and preserves
byte-identical output for all previous native profiles. Strict import rejects
changed metadata, noncanonical/incomplete columns and crossed profiles.

[Structural geometry](Airbender/Proofs/Tables/SllHighParts.lean) retains all 74
actual blocks and six exact partitions. Ten stored templates use the source raw
array helpers and kernel checks of at most 64 queries per calculation. The
largest template contains 1024 entries; the combined templates contain 2046.
[Symbolic periodic assembly](Airbender/Proofs/Tables/SllHighPart4.lean) is proved
over arrays before instantiating those checked sizes/values. Direct imported-data
normalization reached the resident/Lean allocation limits; this staging keeps
the same ceilings and avoids two-million-row enumeration. Every limit/failure
left no owned surviving worker.

[Independent arithmetic](Airbender/Proofs/Tables/SllHighMath.lean) connects the
result to the standard RV32 bitvector shift and truncation. [Internal assembly](Airbender/Proofs/Tables/SllHigh.lean)
combines actual keys, zero padding, tags, full output certificates and canonical
field values. [Regressions](Tests/NativeSllHigh.lean) check shifts zero/one/fifteen/
sixteen/31, top-bit loss, the last surviving bit and its next-bit boundary,
and malformed output/low-padding/packed-key queries. Discarded bits match RV32;
no native implementation defect is established.

Native low-input SLL and high-input SRL remain, followed by faithful dynamic
lookup import, numerical family soundness and initialized execution. Custom
CSR/oracle semantics, general Rust/JSON/compiler refinement and cryptographic
enforcement remain separate.

## Native low-input logical left shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSllLow.lean)
connect original Clean membership to every actual native low-input SLL row.
Membership derives the packed-key bound, both 16-bit output bounds and exact
RV32 left-shift semantics after reconstructing the low/high output limbs.
Carry across bit 16 and truncation past bit 31 follow from the native values;
no output bounds, table equivalence or desired shift result is assumed.

[The actual native export](artifacts/setup/shift-sll-low-native.json) retains
ID 48, compiled offset 266241 and all 2,097,152 rows. Strict literal import checks
its complete canonical four-column data and exact regional metadata. Native
reproduction preserves all previous profiles byte-for-byte; crossed SLL/SRL and
scalar/binary/control profiles reject.

[Checked reuse](Airbender/Proofs/Tables/SllLowColumns.lean) identifies the entire
low-output column with the previously certified native SLL-high output column.
[Structural geometry](Airbender/Proofs/Tables/SllLowParts.lean) retains all 145
high-output blocks: six symbolic prefix partitions and the existing 73-block
SLL-high suffix. [Generic certificate transport](Airbender/Proofs/Tables/BlockTransport.lean)
reuses those proved values after an independently proved shift-sixteen index
translation. [Arithmetic](Airbender/Proofs/Tables/SllLowMath.lean) reconstructs
RV32 results with standard quotient/remainder identities. Existing block
semantics, checked templates and native codec remain unchanged.
Direct imported-column normalization reached the resident watchdog limit;
structural list equality replaces it under unchanged ceilings. The watchdog
confirmed termination of every owned worker after that limit.

[Regressions](Tests/NativeSllLow.lean) check shifts zero/one/fifteen/sixteen/31,
first carry and its preceding input, the final surviving bit and the following
discard boundary, plus malformed low/high/limb/key queries. No native defect is
established. High-input SRL remains before faithful dynamic constraint import,
numerical family soundness and initialized execution; general Rust/compiler
refinement and cryptographic enforcement remain separate.

## Native high-input logical right shift

[Two short public helper claims](Airbender/Review/Helpers/Tables/NativeSrlHigh.lean)
connect original Clean membership to all 2,097,152 actual high-input SRL rows.
Membership derives the packed-key and both output-limb bounds, then exact RV32
logical-right-shift semantics for the input placed in bits 16–31. Reconstruction
uses canonical limbs; no whole-word Mersenne31 cast, desired result or
table-equivalence premise is supplied.

[The actual native export](artifacts/setup/shift-srl-high-native.json) retains
ID 51 and compiled offset 6557697. Strict literal import preserves its complete
four-column data; native reproduction preserves every prior profile byte-for-byte.
Crossed profiles, changed metadata, incomplete/noncanonical data and unknown fields
reject. Compiler/JSON/Rust refinement remains a separate fidelity boundary.

[Checked reuse](Airbender/Proofs/Tables/SrlHighColumns.lean) identifies the entire
high-output column with native SRL-low. [All 146 low-output blocks](Airbender/Proofs/Tables/SrlHighParts.lean)
retain their actual geometry: the initial zero block spans 65,537 rows, ten
periodic templates start one word into each shift and the first shift-eleven
affine block has 2,047 rows. Ten structural template proofs use kernel checks of
at most 64 stored entries per calculation. Five symbolic prefix partitions and
[unchanged generic transport](Airbender/Proofs/Tables/BlockTransport.lean) reuse
73 native SRL-low blocks after an independently proved shift-sixteen translation.
[Arithmetic](Airbender/Proofs/Tables/SrlHighMath.lean) derives both reconstructed
limbs and standard bitvector semantics without two-million-row enumeration.

[Regressions](Tests/NativeSrlHigh.lean) check rotated-template/cross-shift edges,
the shortened affine/reset boundary, shifts zero/one/fifteen/sixteen/31 and final
surviving bits, plus malformed low/high/limb/key queries. No native defect is
established. Helper membership/results are now checked for all four native
logical-shift limb tables. Faithful dynamic constraint import, numerical family
soundness and initialized shift/binop execution remain unfinished; general
Rust/compiler refinement and cryptographic enforcement remain separate.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all one hundred and thirty-seven concrete test modules pass.
- Importer regressions: 492 checks pass.
- Axiom audit: 2291 explicit roots; only propext, Classical.choice and Quot.sound.
- All one hundred and thirty-seven public Review theorems (forty-six circuit claims, sixty-four trace claims and twenty-seven helper claims including the two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 79 unchanged reused files, six native circuit artifacts, fifty native Rust sources plus compiled shift-offset metadata, twenty-one native setup artifacts and four exporter source/manifest/lock files.
- Aliased sources/destination form a nonempty accepted history. A stale alias
  read passes local constraints and is rejected by logical memory matching.
- Public Sail x1/PC reads construct the accepted alias fixture; missing register and byte data reject construction.
- Original-opcode SUB-to-x0 with nonzero source operands passes native constraints and the public Sail theorem.
- Actual ADD bytes build a padded setup and yield public Sail source evidence and native read/terminal bounds. The retained padding is rejected by native equations. A bad zero flag passes local constraints and makes an unbounded write, but lookup membership rejects it.
- U-type raw funct3, sign-extended ADDI, original-opcode x0 decoding and invalid setup capacity regressions pass.
- Actual Sail history realizes the alias fixture; all three reads use the instruction pre-state and the destination writes 246. An initialized original SUB-to-x0 fixture retains nonzero operands/raw result and its masked write is an actual Sail stutter.
- The accepted public alias fixture derives all PC inputs/successors and its terminal bound. An empty-row fixture derives its terminal bound from the actual public initial PC. The native wraparound regression passes through the factored column-only calculation.
- The accepted alias ADD now reaches original Sail retirement with all local interfaces derived. Actual SUB bytes construct the x0 setup; original SUB-to-x0 retires PC+4 with the native data stutter, without caller-supplied operand or Sail-read interfaces.
- Complete execution passes on the alias ADD, original SUB-to-x0 and empty trace. Reversed dependent ADD/ADDI witness rows derive a finite original Sail trace reaching PC 8 and x2=247; no intermediate read/state or final-value premise is supplied.
- Full native RAM load/store and ROM load rows pass, including x0-masked ROM loads. Native UNIMP padding is retained; changed ROM values, unaligned addresses and ROM stores are rejected. Fixed-query arity, table selection and column mapping fail-closed regressions pass.
- Non-padding public ROM data loads both actual write limbs. Native source-plus-immediate address addition, PC increment and clock order pass on full rows; a native witness simultaneously wraps address and PC from 0xfffffffc to zero. Local row interfaces retain explicit inputs; initialized history now derives native clock inputs and word ranges.
- Actual LW/SW bytes and nonempty accepted word-memory traces recover public original Sail source evidence, including LW to x0. Full minus-one padding is retained/rejected by the native store-mask equation. Negative immediates, unsupported subword/unsigned constructors, missing bytes and insufficient capacity are checked. A flag-2 row passes native constraints but fails full decoder membership.
- Actual public LW bytes construct a ROM image; a full native ROM-load row recovers those bytes through the public Sail read theorem. Consistently altered native ROM data is rejected. Native UNIMP tail entries remain present while absent Sail padding bytes remain actual failures. Missing bytes and excessive counts reject extraction.
- Nonempty public LW/SW and x0/ROM-shadow fixtures derive complete Clean history, newest reads, every row/prior clock input and all native word ranges. Actual public bytes build the decoder setup. Omitting a discarded shadow read's initialization token fails logical matching. The shadow fixture explicitly initializes the logical native RAM cell; architectural ROM projection is not claimed.
- Initialized public LW/SW/x0/ROM-shadow fixtures derive native effective addresses, incoming PC ranges/alignment, bounded modular successors and clock/port order through the existing calculations, without local numerical premises.
- Actual source-GPR reads, RAM-load register writes, RAM-store byte writes and x0/ROM-shadow cell stuttering are derived from nonempty initialized histories. Reversed dependent SW/LW rows construct real public decoder bytes and derive an intermediate store state, subsequent read of 123 and destination register write; no intermediate state/read or final-value premise is supplied. These are cell-transfer results, not original instruction execution claims.
- Ordinary and x0 ROM-load shadow ports satisfy the general native value-preservation theorem. A real changing RAM store is excluded from every address in the readonly shadow region. Native matching/initialization obligations remain intact.
- Whole-address Clean projection preserves consistency and newest writes. Separate architectural/ghost initialization derives native clocks, unique addresses and x0 preservation without reading shadow bytes from Sail. Accepted ordinary/x0 ROM loads retain their native shadow event, derive actual masked Sail register writes and final architectural matching, even with missing shadow bytes and distinct native shadow/ROM values. No expected read, intermediate state or table-equivalence premise is supplied. This does not bind physical zero boot or prove original LOAD/STORE execution.
- The projected initializer also derives every full native read, actual write and terminal word bound using the existing shared decreasing-time induction and native decoder/mask rules unchanged. Ordinary/x0 ROM-load regressions retain bounds for shadow cells with no Sail bytes, without per-row/port range premises.
- The projected initializer and actual public decoder now discharge every native address/PC/clock interface through the same calculations as the full-image boundary. General retained-port transport derives original Sail source-GPR reads and actual masked writes for ordinary/x0 ROM loads with unreadable shadows. The reversed dependent RAM store/load regression now exercises retained RAM reads/writes through these same transport lemmas, deriving its intermediate state and later read unchanged.
- Initialized projected histories preserve all ROM-prefix byte entries and successful public ROM extractions. The reversed SW/LW regression derives a RAM change from zero to 123 while retaining both original instructions and their two-word public ROM image; missing byte 16 stays absent. Ordinary/x0 ROM loads retain absent shadow bytes and their full native shadow refreshes. Code-window bounds come from actual indexed setup construction under the public native-ROM program-size bound; no expected later fetch is supplied.
- Public Machine/PMP/PMA configuration now survives complete initialized projected native histories. The same reversed SW/LW fixture initializes actual public CSRs and reaches original Sail virtual-memory store/load results through checked translation, permissions and platform helpers. Native matching and public construction derive all source/address/value/intermediate-state inputs. Original ROM/RAM clauses and row preparation/retirement are now checked below; general trace composition is now checked above.
- Initialized ordinary/x0 ROM fixtures derive actual extraction, original virtual reads and original LW clause execution to the actual masked-write after-state. Native shadow value 123 stays matched and differs from the actual loaded ROM word 0xc0001073. No expected-read/value or desired-state premise is supplied; original x0 decoding is retained. Original RAM clauses and row preparation/retirement are checked below; general trace composition is now checked above.
- The unchanged reversed accepted native SW/LW fixture now reaches the original instruction clauses in its derived states. Native/public construction supplies selectors, source/address facts and actual reads. The later load reads the real preceding store value 123 and reaches the actual destination write; no intermediate state, expected read or desired result is supplied. All previous cell, code, ROM and virtual-memory regressions remain intact.
- The same original clauses now pass native row preparation/retirement. Ordinary/x0 ROM loads retain actual memory behavior and reach native PC 4; reversed SW/LW normal steps start from the actual public Sail state and reach PC 8, RAM 123 and x3=123 from native terminal matching. The combined proof derives addresses/native successors and dispatches original instructions without per-row read, prepared-state or desired-PC inputs. General finite trace/fetch composition is now checked above.
- General fetched/decoded word-memory execution passes on reversed dependent SW/LW, ordinary/x0 ROM loads and an empty native trace. The same general relation reaches actual PC 8 and native terminal RAM/x3=123. Native matching retains independent shadow value 123 while actual ROM reads 0xc0001073. All local address domains are derived from public cells/seeds; no per-row range/read/order/state/result premise is supplied.
- Fixed-zero native boot passes on original ordinary/x0 LW fixtures with all actual GPRs zero, real public instruction/ROM bytes and fully matched zero native shadows. General execution derives PC four and actual masked destinations; full native paths derive terminal shadow zero. Invented seed values and an actual nonzero public GPR are rejected. Symbolic padding checks retain input words and distinguish zero loader padding from raw-table UNIMP fallback; absent Sail padding bytes remain actual failures.
- Explicit Sail byte padding derives full four-MiB extraction, original zero-profile/configuration/setup preservation and complete native boot execution on ordinary/x0 loads. Prefix and out-of-ROM bytes are retained, the last ROM byte is zero and a formerly missing tail word becomes readable. Missing/oversized supplied prefixes reject construction. All large extents are handled symbolically; no evaluated large certificate or supplied padding/coverage/read/state/result premise is used.
- Exact setup metadata for both native artifacts and fifteen added importer regressions pass. The active four-column tagged row model has exactly the existing ROM/separator meanings, including every dummy/padding tuple. Nonempty original Sail bytes and explicit zero padding derive actual reads from tagged ROM membership; altered words and wrong padding tags are rejected. The normalized final setup row is explicitly outside this model's lookup domain; actual Rust/export/LDE and argument correspondence remains separate.
- The standalone native exporter passes offline locked checking and exact fixture reproduction. Little-endian binary image/text inputs reproduce the fixture; partial words and oversized inputs reject before output. Lean certifies all actual regional ROM/separator/range values, the entire unsupported decoder tail and the loader's image zeros; original LW/SW/x0 and explicit UNIMP/sentinel regressions pass. Compressed-field, extent, region, tag and unknown-field mutations fail closed. Parse/emission, general Rust/compiler refinement and physical trace/LDE/argument connections remain separate.
- Sparse public construction retains actual unsupported interior words at their original PCs and rejects missing/effectful inputs. Native equations derive hole/tail exclusion, original Sail sources, canonical decoder words/alignment and exact x0 flags. The second native export reproduces exactly and its entire decoder matches constructed public Sail data. A full native x0-load constraint witness at PC 12 recovers actual source evidence beyond the UNIMP hole; missing bytes/capacity and all post-hole fields pass. Sparse initialized execution and arbitrary-program Rust refinement remain separate.
- Sparse initialized original execution passes with real code/register/CSR/RAM bytes, complete native matching and actual exported slot-three membership. The existing full x0-load witness starts at public PC 12, retains the PC-four hole, and derives terminal PC 16, RAM 123 and x0 zero. The same strict initialized execution, boot and padding regressions remain intact.
- Both shared scalar prefixes reproduce exactly from the native API/extracted timestamp clause. Symbolic proofs cover every actual value and modeled active filler row, retaining repeated zero rows in the domain and excluding normalization. Existing Clean range helpers have proved exact membership connections. Prefix/padding/endpoints, both compiled placements and fourteen strict importer regressions pass. No full trace is evaluated; physical Rust/argument enforcement remains separate.
- Native control PC bounds pass for all five supported packed masks. A complete JAL -4 witness retains canonical target 0xfffffffc; its noncanonical high-limb variant passes all native polynomials and the other fifteen queries but is rejected by the actual candidate-high range query. No terminal range or verifier-PC closure premise is supplied.
- Public control decoding now derives all local decoder inputs from original Sail bytes and full sparse/padded membership. The full JAL -4 witness uses actual raw funct3 seven and derives outgoing PC bounds without a mask premise; tag-zero mismatch, x0 comparisons/jumps, all branch tags, unsupported holes/tail and missing bytes/capacity regressions pass. The malformed high-PC variant retains real public membership and all polynomials but fails the native range query. Initialized original control execution remains open.
- The native control decoder prefix reproduces exactly and every slot equals the actual public Sail constructor. Raw JAL tag 7, original post-hole SLTIU-to-x0 fields, public text, complete tail, crossed importer profiles and tag-zero rejection pass. The accepted full JAL row instantiates the short exported-decoder source/PC claim.
- Native control clocks and all three imported ports discharge the shared history contract. A full JAL -4 history starts from actual Sail x0/x1/PC reads, consumes its aliased readonly refresh and retains the actual link write. Stale local reads pass native constraints but fail memory matching; explicit missing-register data rejects initialization. Lower-clock carry, every derived port effect and exact terminal clock accumulation pass.
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.

## Complete compiled shift/binop lookup projection

[The native artifact](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) now imports
all 47 quadratic/three linear equations, eight timestamp queries and four dynamic
lookups. Physical witness selectors 24/28/32/36 resolve to logical variables
42/46/50/54 and remain evaluated fourth Clean query fields. Setup, decoder,
clock and all three direct memory ports have checked kernel bindings.

[The tagged table](Airbender/Review/Circuits/ShiftBinop/Tables/Native.lean) reads
all twelve actual exported regions in compiled offset order, spanning 10,817,537
rows. It retains the native zero row and every tag without inserting another
inactive row. [Structural inclusion proofs](Airbender/Proofs/ShiftBinop/NativeLookup.lean)
cover every row of every region. Existing binary/scalar/four-limb certificates
supply mathematical helper results separately. Direct closed-data regression
calculations hit Lean's allocation cap; structural row transport replaces them
under unchanged ceilings, with no surviving owned workers after the failure.

The CSR-properties region uses the exact native compilation-test generator:
nondeterminism enabled with an empty delegation CSR list. [Its actual data](artifacts/setup/shift-csr-properties-native.json)
retains ID 25, offset 196609 and all 4096 rows. Native source explicitly requires
separately configured CSR contents for proving/setup; this profile does not bind
runtime CSR setup or establish custom CSR/oracle/delegation execution semantics.
The strict regional importer rejects an unbound runtime profile.

[Kernel regressions](Tests/ShiftArtifact.lean) check all query expressions,
selector evaluation, metadata/placements and actual zero/CSR/final native rows.
[Importer regressions](Tests/ArtifactImport.lean) reject missing/extra/wide/short
queries, crossed/unknown selectors, unmapped/aliased physical variables, changed
offsets/extents and malformed/crossed CSR data. All native profiles reproduce
byte-for-byte. This closes the concrete local import prerequisite; numerical
shift/binop soundness and initialized original Sail execution remain unfinished.
General Rust/JSON/compiler refinement and cryptographic argument enforcement
remain separate. No native implementation defect is established.

## Accepted native shift/binop lookup resolution

[The short lookup claims](Airbender/Review/Circuits/ShiftBinop/Lookups.lean)
now extract all four actual tagged queries from original Clean constraint
acceptance. The fourth fields are the evaluated witnesses at logical columns
42/46/50/54. Accepted canonical selectors lie exactly in the twelve stored tags;
[structural partition and tag uniqueness](Airbender/Proofs/ShiftBinop/NativeRegions.lean)
exclude cross-region substitution across all 10,817,537 actual rows.

[Resolution assembly](Airbender/Proofs/ShiftBinop/NativeResolution.lean) derives
exact binary/scalar/four logical-shift helper membership from each selected tag.
Existing helper result proofs therefore apply directly to accepted native queries,
without a table-equivalence or desired-result premise. Tag zero requires all
three fields to be zero; it does not disable arbitrary inputs or outputs. The
CSR tag resolves only the recorded compilation fixture, with the runtime setup
and custom instruction boundaries unchanged.

[Combined-table regressions](Tests/ShiftLookups.lean) cover valid binary and all
shift-table boundaries, incorrect results/selectors, unsupported tags, nonzero
inactive data, crossed SLL regions and canonical field selector wraparound.
These are checked lookup connections, not complete numerical circuit or
initialized shift/binop Sail execution. Operation routing and row/state assembly
remain the next milestone. No native implementation defect is established.

## Decoded native shift/binop operation routing

[The short routing claim](Airbender/Review/Circuits/ShiftBinop/Routing.lean)
now connects original public-byte construction and actual native decoder membership
to all four table selectors, register/immediate operand selection and zero ordinary
delegation-request multiplicity. [Observable references](Airbender/Review/Circuits/ShiftBinop/RoutingModel.lean)
retain the six native bits and distinct raw funct3. SLL uses tags 47/48/49/0,
SRL 47/50/51/0 and SRA 47/52/50/51; each binary form uses its original funct3
in all four slots. SRAI retains the native immediate's funct7 payload.

[Selector recovery](Airbender/Proofs/ShiftBinop/Selectors.lean) derives Booleanity
and a canonical mask at most 63 from actual equations. [Original source recovery](Airbender/Proofs/ShiftBinop/Decoder.lean)
excludes unsupported slots and the complete minus-one tail. [Routing assembly](Airbender/Proofs/ShiftBinop/Routing.lean)
derives the observed tags and operands without supplied operation bits, table
choices, output values or a table-equivalence premise. Logical column 37 is the
native request multiplicity; its zero value for ordinary forms does not establish
worker/request protocol soundness or custom CSR semantics.

[Regressions](Tests/ShiftRouting.lean) check complete native constraints and all
lookups for twelve ordinary forms and their x0 variants, then apply the public
claim using actual original byte reads. All 96 fixture queries have native-table
membership certificates. Six [four-row groups](Tests/ShiftRoutingPart0.lean) keep
closed equation checks and symbolic native query transport within unchanged
budgets. Wrong sign-fill tags, wrong immediate selection and injected CSR bits
reject. Numerical word results, actual Sail register reads, initialized family
history/execution and runtime CSR setup remain separate. No native defect is
established.

## Native binary numerical results and actual x0 writes

[The short public binary claim](Airbender/Review/Circuits/ShiftBinop/Binary.lean)
now derives exact native XOR/OR/AND results for register and immediate forms from
original public-byte construction, native decoder membership and accepted native
constraints. [References and observables](Airbender/Review/Circuits/ShiftBinop/BinaryModel.lean)
retain the actual first-source limbs, selected second operand, selected result
and masked destination write. Both input words and the selected result are
bounded conclusions, including when the decoded destination is x0.

[Four-query extraction and native equation assembly](Airbender/Proofs/ShiftBinop/BinaryQueries.lean)
retain the actual Mersenne31 inverse of 256, 8388608. Every accepted byte key and
result is below 256; native equations therefore reconstruct six canonical limbs.
[Word assembly](Airbender/Proofs/ShiftBinop/BinaryValues.lean) uses original bitvector
concatenation lemmas to prove exact RV32 operations, preserving full word values
above the field modulus. [Actual masking and decoded assembly](Airbender/Proofs/ShiftBinop/BinaryResults.lean)
derive discarded x0 writes from native destination equations and the public
entry's zero flag. No operand-bound, selected-output, table-equivalence or
individual operation-bit premise is added to the public claim.

[Regressions](Tests/ShiftBinary.lean) reuse complete accepted native fixtures for
all twelve binary register/immediate/x0 cases, apply the public result root and
retain negative immediates, full RV32 values above Mersenne31 and nonzero selected
results discarded at x0. Corrupted byte reconstruction, selected limbs and x0
writes reject. No native implementation defect is established. Native shift
numerical assembly, family clocks/ports, initialized register/history transport
and original Sail instruction execution remain open. Runtime CSR setup, worker
protocol enforcement, cryptography and general Rust/JSON/compiler refinement
remain separate boundaries. The preceding sections are earlier checkpoints.

## Native shift contributions and selected-word assembly

[The short shift contribution claim](Airbender/Review/Circuits/ShiftBinop/Shifts.lean)
now derives the actual native low-five-bit truncation, all three contribution
slots and exact selected-word assembly for SLL/SRL/SRA and their immediate forms.
[References and observables](Airbender/Review/Circuits/ShiftBinop/ShiftModel.lean)
retain actual key/result columns, source columns and native slot order. The first
query bounds the selected low operand below 65536, computes its remainder modulo
32 and forces its padding field to zero.

[Native equation assembly](Airbender/Proofs/ShiftBinop/ShiftEquations.lean) recovers
each packed source/amount field equation from accepted constraints. [Contribution
resolution](Airbender/Proofs/ShiftBinop/ShiftParts.lean) connects each actual tagged
query to the checked native SLL/SRL/sign-fill helper and derives key bounds, both
output-limb bounds and exact canonical-key RV32 contributions. SLL/SRL's inactive
third slot is the literal native zero row. SRA uses sign fill, low-input SRL and
high-input SRL in that order. [Selected assembly](Airbender/Proofs/ShiftBinop/ShiftContributions.lean)
lifts both native three-limb sums without Mersenne31 wrap and derives exact RV32
addition of the contributions; no preselected result or input-range premise is
added to the public claim.

[Regressions](Tests/ShiftContributions.lean) reuse complete accepted native rows
for all twelve shift register/immediate/x0 cases and apply the public root.
SRAI retains encoded immediate 1055, truncates to 31 and combines 0xfffffffe,
zero and one. SLLI/SRLI shift-31 and discarded x0-selected values pass; corrupt
packed keys, nonzero inactive contributions and omitted sign fill reject.
This checkpoint states contributions of actual canonical packed keys. Binding
their quotient/remainder to initialized bounded source reads, canonical selected
limbs and complete architectural shifts remains unfinished, as do family clocks,
initialized register/history transport and original Sail instruction execution.
Runtime CSR setup, worker protocol enforcement, cryptography and general
Rust/JSON/compiler refinement remain separate. No native defect is established;
earlier sections retain their checkpoint scope.

## Native shift/binop initialized clocks and memory history

[The short public history claim](Airbender/Review/Trace/Families/ShiftBinop/History.lean)
now derives complete Clean memory consistency and latest preceding reads for
all three native ports from original Sail public register/PC seeds and accepted
native state/memory matching. The [native registry](Airbender/Review/Helpers/Context/ShiftBinop.lean)
retains the actual constraints, decoder metadata, clock columns and memory ports.
[Metadata checks](Airbender/Proofs/ShiftBinop/ClockMetadata.lean) retain the complete
10,817,537-row tagged setup geometry. [Clock extraction](Airbender/Proofs/ShiftBinop/Timestamp.lean)
uses the actual two carry equations and all eight timestamp queries. The
[shared instance](Airbender/Proofs/Trace/Families/ShiftBinop/History.lean) derives
four-tick advancement, strict port order and all row/prior bounds and alignment
from initialization and matching. No local clock, schedule or expected-read
premise is added to the public claim.

[Complete initialized regressions](Tests/ShiftHistoryFixture.lean) check state
and memory permutations for all twenty-four ordinary register/immediate/x0 rows,
with original Sail seeds for x0, x1, x2, x3 and PC. [Native local checks](Tests/ShiftHistoryRows.lean)
correct only the last prior-clock column for six immediate/x0 aliases: the second native port
refreshes x0 at time five, which the destination port must consume. All fifty
native equations, eight timestamp queries and four unchanged tagged queries
pass. All six stale alternatives satisfy local constraints but fail native
logical memory matching. [Public applications](Tests/ShiftHistory.lean) derive
complete history, latest reads and clock inputs without separately supplied
bounds, alignment or ordering. This confirms the required matching behavior;
no native implementation defect is established.

Source-word bounds and canonical packed-key binding remain unfinished, as do
actual Sail cell transfers and original shift/binop instruction/fetched execution.
Runtime CSR setup, worker protocols, cryptography and general Rust/JSON/compiler
refinement remain separate boundaries. Earlier sections retain their checkpoint
scope.


## Initialized shift/binop word bounds and canonical source keys

[The short value claim](Airbender/Review/Trace/Families/ShiftBinop/Values.lean)
now derives every native read, actual write and terminal word range from original
public code construction, actual Sail seeds/PC and accepted native matching.
[Native write preservation](Airbender/Proofs/Trace/Families/ShiftBinop/Values.lean)
uses full native decoder membership to select binary results or shift sums and
retain the exact x0-masked destination. Readonly ports keep their actual refreshes.
The unchanged shared time induction supplies the earlier source bounds; no
per-row operand/read/range or desired-result premise is added.

[Internal limb references](Airbender/Proofs/ShiftBinop/LimbModel.lean) preserve two
native 16-bit source limbs, all 32 shift amounts and SRA's sign-fill/low/high
order. Separate [SLL](Airbender/Proofs/ShiftBinop/SllLimbBounds.lean),
[SRL](Airbender/Proofs/ShiftBinop/SrlLimbBounds.lean) and
[SRA](Airbender/Proofs/ShiftBinop/SraLimbBounds.lean) calculations prove that every
actual contribution half sum is canonical, including both sign domains. No v3
byte-table layout or unchecked overlap assumption is used.

[The short source claim](Airbender/Review/Trace/Families/ShiftBinop/Sources.lean)
now derives exact natural packed-key values and their source/amount remainders
and quotients, together with actual source/selected bounds. [Observables](Airbender/Review/Circuits/ShiftBinop/SourcesModel.lean)
retain actual native columns and literal inactive zero slots. [Field lifting](Airbender/Proofs/ShiftBinop/ShiftSourceBounds.lean)
uses initialized source bounds to exclude Mersenne31 wrap; [trace assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Sources.lean)
combines those bounds with original decoded entries and accepted contributions.
Canonical-source binding is derived, rather than postulated.

[Original-byte fixtures](Tests/ShiftValuesFixture.lean) preserve the actual native
25-slot public program and replay the unchanged original Sail decoder after GPR/PC
updates with the same misa image. [Initialized applications](Tests/ShiftValues.lean)
cover all twenty-four ordinary/x0 rows and all twelve concrete shift cases,
including corrected readonly x0 alias clocks and bounded discarded selected words.
Whole architectural shift results, actual Sail cell/GPR transfers and original
instruction/fetched execution remain unfinished. Runtime CSR configuration,
worker protocols, cryptographic enforcement and general compiler refinement stay
separate. This is proof coverage, not a new defect finding; the findings bar and
historical coverage archive are unchanged.

## Initialized whole shift/binop numerical results

[The short public result claim](Airbender/Review/Trace/Families/ShiftBinop/Theorems.lean)
now derives exact canonical selected and actual destination limbs for all six
ordinary SLL/SRL/SRA/XOR/OR/AND families, including immediate forms and discarded
x0 writes. Actual public Sail code construction, public seed/PC reads, complete
native matching and full decoder membership supply all premises. No source/range,
operation-selector, desired-result or expected-write premise is supplied.

[Numerical references](Airbender/Review/Circuits/ShiftBinop/ResultsModel.lean)
retain whole RV32 operations and architectural low-five-bit shift amounts.
Separate [SLL](Airbender/Proofs/ShiftBinop/SllLimbResult.lean),
[SRL](Airbender/Proofs/ShiftBinop/SrlLimbResult.lean) and
[SRA](Airbender/Proofs/ShiftBinop/SraLimbResult.lean) calculations reconstruct
whole results from the actual native two-limb contribution order across all 32
amounts. SRA derives the architectural sign bit; its positive and negative
calculations use separate declarations to retain default proof budgets. No
memory or heartbeat ceiling is raised.

[Native assembly](Airbender/Proofs/ShiftBinop/Results.lean) combines canonical
source-key lifting with accepted contributions and exact decoded x0 masking.
It proves low-limb modulo 32 equals whole-operand low-five-bit extraction,
retaining SRAI's encoded funct7 payload. [Initialized assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Results.lean)
supplies source bounds from the unchanged shared history induction and proves
every selected/write limb equals its canonical numerical result encoding.

[All twenty-four initialized regressions](Tests/ShiftResults.lean) apply the
public claim and derive concrete outputs for every ordinary/x0 fixture, retaining
negative SRA, shifts 31, SRAI 1055→31, XORI -1, ORI -2048 and ANDI 2047.
Original Sail cell/GPR transfers, instruction clauses, PC retirement and fetched
execution remain unfinished. Runtime CSR/worker protocols, physical cryptographic
enforcement and general compiler refinement remain separate. This is coverage,
not a new defect finding; the finding standard and historical archive are unchanged.

## Initialized original Sail shift/binop register histories

[The short public register-history claim](Airbender/Review/Trace/Families/ShiftBinop/Registers.lean)
now constructs actual original Sail GPR reads/writes, all native-clock-ordered
segment states, final cell matching and code/misa preservation from actual public
code/seeds/PC and full native matching/decoding. Public tracked-cell alignment
remains explicit. No expected read, intermediate state, result, write or decoder
replay is supplied. [Observables](Airbender/Review/Helpers/Memory/ShiftBinop.lean)
retain the first two readonly accesses and the actual masked destination port;
all three reads use the same real row pre-state, including aliases.

[Native x0 preservation](Airbender/Proofs/Trace/Families/ShiftBinop/ZeroRegister.lean)
uses the original rd/zero-flag lookup columns and actual mask equations 39/40,
with write columns 59/60. Readonly refreshes preserve their exact reads. The
unchanged shared decreasing-time and Clean-to-Sail realization/grouping proofs
derive the actual intermediate cell histories. [Source-entry recovery](Airbender/Proofs/Trace/Families/ShiftBinop/Decoder.lean)
uses the complete native padded decoder and rejects every sentinel-tail row.

[The three port transport declarations](Airbender/Proofs/ShiftBinop/PortReads.lean)
are copied unchanged from the pinned original source and checked against actual
v2 port/decoder metadata. [Code/configuration frames](Airbender/Proofs/Trace/Families/ShiftBinop/CodeHistory.lean)
use native register-space addresses and the unchanged original stateful Sail
misa-frame theorem to replay decoding after real GPR updates. [Internal assembly](Airbender/Proofs/Trace/Families/ShiftBinop/RegisterHistory.lean)
derives every row's source/destination transfers and all segment states.

[All twenty-four regressions](Tests/ShiftRegisters.lean) derive the original
entry from its actual native PC query, original Sail transfers, actual numerical
result writes and preserved code/misa. All twelve original x0 variants preserve
the entire Sail data state, including six immediate/x0 readonly aliases.
Original instruction clauses, PC preparation/retirement and complete fetched
execution remain unfinished. Runtime CSR/worker protocols, physical cryptographic
enforcement and general compiler refinement remain separate. This is coverage,
not a new defect finding; the findings bar and historical archive are unchanged.

## Initialized original Sail shift/binop clauses

[The short public clause-history claim](Airbender/Review/Trace/Families/ShiftBinop/Clauses.lean)
now derives original Sail clause execution for all six ordinary operations and
all twelve register/immediate forms from actual public code/initialization and
full accepted native matching/decoding. [Observables](Airbender/Review/Helpers/Memory/ShiftBinopClauses.lean)
retain original instructions, actual constructed GPR histories and the same
native row pre/post states. Source reads, source bounds, selected operands,
masked writes and intermediate states are derived rather than supplied.

[Internal clause assembly](Airbender/Proofs/ShiftBinop/Clauses.lean) executes the
original pinned register/immediate clauses through the unchanged original
dispatcher. Actual native routing and public immediate columns determine the
complete selected operand. Sign extension is retained; SRAI's original encoded
funct7 bits are proved to leave its architectural low-five-bit shift count
unchanged. Actual native numerical results and masked destination writes reach
the original clause's same after-state, including original x0 opcodes and aliases.
[Initialized assembly](Airbender/Proofs/Trace/Families/ShiftBinop/Clauses.lean)
derives source bounds and exact original entries from the existing initialized
history and actual original public decoding.

[All twenty-four complete regressions](Tests/ShiftClauses.lean) now construct
original Sail clause executions and actual native transfers with preserved
code/misa. All twelve original x0 variants actually execute and preserve the
whole data state, including all six immediate/destination aliases. Original
RV32 profile decoding still rejects shift amounts 32 and 63. PC preparation,
retirement and complete fetched execution remain next. Custom CSR/worker
protocols, physical cryptographic enforcement and general compiler refinement
remain separate. This adds coverage, with no new defect finding; the findings
standard and historical archive are unchanged.

## Initialized original fetched shift/binop execution

[The short public fetched-execution claim](Airbender/Review/Trace/Families/ShiftBinop/FetchedExecution.lean)
now derives finite original Sail execution and actual terminal PC/cell reads for
the selected ordinary SLL/SRL/SRA/XOR/OR/AND profile, including all twelve original
register/immediate forms and discarded x0 variants. Actual public bytes and
initialization, full accepted native matching/decoding and public tracked-cell
alignment are visible premises. No expected read/result, local PC bound or
alignment, intermediate state, decoder replay or table equivalence is supplied.

[Native PC assembly](Airbender/Proofs/ShiftBinop/PC.lean) uses the actual shift
carry gates, inverses and output equations 41..46 and Boolean indices 6/7. Original
public query/setup construction derives the incoming canonical aligned PC;
accepted native equations derive outgoing bounds and modular +4. [Complete row regressions](Tests/ShiftPC.lean) retain low-limb carry and full RV32 wraparound.
[Original retirement assembly](Airbender/Proofs/ShiftBinop/Execution.lean) transports
the actual native history through original nextPC preparation, the retained
original clause and original retirement. [The local public claim](Airbender/Review/Trace/Families/ShiftBinop/Execution.lean)
constructs all actual row states and retired steps; [observables](Airbender/Review/Helpers/Memory/ShiftBinopExecution.lean)
keep original dispatch, native states and the exact successor PC visible.

[Stateful fetched composition](Airbender/Proofs/Trace/Families/ShiftBinop/Composition.lean)
uses actual native GPR history to preserve code/misa and replay original decoding
in each actual pre-state. Native PC matching composes the original fetched normal
steps through arbitrary accepted finite row histories, including empty traces.
Raw terminal PC bounds follow from native/public matching. [All twenty-four retirement regressions](Tests/ShiftExecution.lean) derive actual states and all
twelve x0 retirements; [fetched regressions](Tests/ShiftFetched.lean) derive exact
terminal PCs and GPR values for every ordinary/register/immediate/x0 case, plus
empty execution from actual public initialization. Remaining ordinary/subword
memory coverage, runtime CSR setup, delegation and unified protocol/terminal
boundaries remain separately scoped. General compiler refinement and physical
cryptographic enforcement are unchanged boundaries. This is coverage progress;
no new native-v2 defect is established and the findings standard is unchanged.

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

## Historical coverage and boundary notes

The following 71 entries were accumulated in the former Findings register through
20 October 2026. They record successive proof checkpoints, scope boundaries and
positive/negative regressions. **They are not 71 defects or vulnerability findings.**
Earlier statements retain their snapshot scope; the latest sections above describe
subsequent completed connections. The [findings register](FINDINGS.md) now separates
confirmed defects, assessed exclusions, unresolved bindings and unassessed v3
candidates under the same standard as the pinned v3 review.

| Case | Evidence and disposition |
| --- | --- |
| V2 PC rollover | [Native rollover fixture](Tests/PC.lean) accepts PC 0xfffffffc to zero. The v2 proof preserves this modular behavior instead of importing the source artifact's no-overflow conclusion. [Public native PC assembly](Airbender/Review/Trace/PC.lean) now derives incoming alignment/bounds and outgoing/terminal bounds, retaining RV32 indexed-PC truncation. Actual Sail retirement and complete execution are checked below. This is a supported aligned path, not a reported implementation defect. |
| Local decoder/history interfaces | [Model](Airbender/Review/Circuits/AddSub/Model.lean) explicitly retains the packed decoder mask, x0 flag, preprocessing, input bounds, initial PC alignment and original Sail reads. [Selectors](Airbender/Proofs/AddSub/Selectors.lean) derives individual selector bits. Public decoding and initialized history now derive value/read/PC facts. [Decoded row assembly](Airbender/Proofs/Trace/Arithmetic.lean) now derives all local interfaces and original Sail row retirement. [Initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/Theorems.lean) now composes these rows to exact terminal PC/cells. Remaining families and physical argument enforcement are separate. |
| Native clock boundary | [Clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives native advancement and port order; all per-row/prior bounds and alignment now follow from accepted logical matching and only initial clock boundaries. Typed port/state metadata is checked separately from memory-argument enforcement. |
| Stale alias reads | [Initialized-history regression](Tests/InitializedHistory.lean) shows that a second read reusing the seed timestamp passes local native row constraints but fails actual logical memory matching. This validates the separate memory boundary; it is not a v2 implementation vulnerability. The complete-history theorem derives newest preceding reads. |
| Logical initial image | [Trace memory claim](Airbender/Review/Trace/History.lean) takes explicit seed/final tokens and logical matching. [Public constructors](Airbender/Review/Helpers/Memory/PublicImage.lean) now bind seeds and initial PC to actual Sail state; native word bounds and actual subsequent Sail cell reads/writes are derived, while physical boot/profile binding remains pending. No desired read/result or table-equivalence premise was introduced. |
| Decoder-owned zero flag | Native equations 24/25 use decoder variable 8 only to mask raw output into actual writes. Its Boolean/value relation comes from decoder matching, so history bounds cannot be promoted from raw-output bounds alone. Full padded logical decoder membership now recovers the flag; native masked-write and initialized-history word bounds follow. [A bad-flag fixture](Tests/InitializedHistory.lean) passes local equations and has an unbounded write, but full lookup membership rejects it. This validates the separate argument boundary, not an implementation defect. |
| V2 discarded writes retain decoding | Native v2 preprocessing retains the original opcode mask/operands for rd=x0, then masks the actual destination write. The prior local interface inherited an unnecessary source-style NOP restriction; it is removed. [Original Sail SUB x0,x1,x2](Tests/CircuitRows.lean) now has a checked nonzero-operand native row and public theorem application. Native masked-write equations now prove x0 preservation for initialized history; [the complete SUB fixture](Tests/X0History.lean) derives actual Sail stuttering without NOP preprocessing. [Retirement regressions](Tests/X0History.lean) now construct actual SUB bytes and derive original Sail PC retirement from these facts. No Rust behavior was changed. |
| V2 decoder padding | The native all-minus-one padding tail is retained in the logical setup. [Packed-mask bounds and padding exclusion](Airbender/Proofs/Trace/DecoderSetup.lean) reject it from actual ADD/SUB equations/Boolean bits, with no per-row PC-bound or desired-field assumption. Other setup/filler domains remain unassessed. |
| Selected setup construction | [Public setup](Airbender/Review/Helpers/Decoder/Setup.lean) reads actual bytes and original Sail decoding for the five arithmetic opcodes. It rejects missing/unsupported/effectful entries and retains native-shaped capacity/padding. General Rust generation/export fidelity and mixed/custom programs remain separate; no table-equivalence premise is used. |
| V2 word-memory ROM queries | [Native transfer theorem](Airbender/Review/Circuits/WordMemory/Theorems.lean) derives alignment, exact public ROM data, port selection, masked loads and RAM-only stores from all native equations/queries. Both ROM queries are unconditional, including RAM shadow queries; ROM loads retain a discarded readonly RAM access. Complete table models retain native 0xc0001073 UNIMP padding. The native address calculation now derives low/high carries and RV32 wraparound under source/immediate bounds. Checked PC/clock laws retain rollover and native port offsets under explicit local inputs. Public LW/SW decoding now recovers actual Sail source evidence and exact zero flags/PC/immediate facts. Initialized logical reads/ranges now include discarded ROM-shadow accesses. Actual Sail cell histories now realize the full supplied native image. Separate architectural projection is now checked below; original instruction execution is checked below; physical boot/ROM/setup binding remains pending. These are supported native behaviors, not implementation defects. |
| V2 word-memory decoder boundary | [Public decoder theorem](Airbender/Review/Trace/Families/WordMemory/Decoder.lean) uses actual LW/SW bytes and full padded membership. Native store-mask Booleanity rejects the minus-one tail; original x0 loads and sign extension remain intact. [A flag-2 regression](Tests/WordMemory.lean) passes the complete native row constraints, but decoder membership rejects it. This confirms the separate decoder-owned flag boundary; it does not establish an implementation vulnerability. |
| Public ROM prefix versus Sail padding | [Extraction and read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) derive native ROM data from actual public Sail bytes within the extracted prefix. Full extraction covers every ROM address. Native UNIMP padding is retained, but extraction does not populate absent Sail padding bytes; [the boundary regression](Tests/WordROMImage.lean) preserves that actual read failure. Physical boot/padding/shadow-state binding remains open. No table-equivalence or expected-read premise was added. |
| Discarded ROM-shadow participation | [Initialized native history](Airbender/Review/Trace/Families/WordMemory/History.lean) retains all three ports, including the readonly RAM port of an x0 ROM load. [The omitted-shadow regression](Tests/WordMemoryHistory.lean) fails actual memory matching; accepted fixtures derive newest reads, clocks and ranges without per-row answers. The shadow fixture explicitly initializes the native RAM cell. All native RAM accesses below four MiB are now proved value-preserving; the actual matching still retains their timestamp refreshes. Whole-address projection now omits these addresses from architectural Sail histories while retaining full native matching; physical boot/ROM binding remains open. This is not a native implementation defect. |
| Initialized native numerical inputs | [Native-row assembly](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) now discharges source/immediate bounds, PC bounds/alignment and native clock inputs from actual public construction and accepted logical history/decoding. Existing native calculations derive address addition and modular PC successors. Actual Sail cell histories are now checked for the supplied native image; the separate projected history is checked below, while original instruction execution is checked below; physical boot/ROM binding remains open. No desired address/PC result was added as a premise. |
| Sail cell realization versus architectural ROM | [Actual cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean) derive all transfers/states and hardwired x0 preservation from native matching, public seed construction and decoder membership. The existing seed image still binds every supplied native RAM cell, including shadows, to that Sail state. [RAM transfer and dependent store/load regressions](Tests/WordMemorySailHistory.lean) are checked; the separate architectural projection is checked below. Original LOAD/STORE execution is checked below; physical boot/ROM binding remains open. No expected-read, intermediate-state or final-value premise was added. |
| Architectural shadow erasure | [Projected histories](Airbender/Review/Trace/Families/WordMemory/Projection.lean) preserve Clean consistency/latest values for retained addresses and derive actual Sail transfers without reading shadow bytes. [The separate initializer](Airbender/Review/Helpers/Memory/ShadowImage.lean) obtains architectural seeds from actual Sail reads and retains public canonical native shadow values independently. Clocks, unique addresses, x0 writes and all full native read/write/terminal word bounds are derived. The existing range induction and native write rules are reused unchanged, including erased shadow accesses. [Ordinary/x0 ROM regressions](Tests/WordMemoryProjection.lean) retain every native event while a shadow read fails in Sail and its value differs from the ROM result. These logical seeds do not assert the physical native zero-boot profile; original instruction execution is checked below; ROM-table/boot binding remains open. |
| Projected native row interfaces | [Native effects](Airbender/Review/Trace/Families/WordMemory/Inputs.lean) now derive the complete native address/PC/clock interfaces from the separate initializer and actual public decoding. [Retained-port transport](Airbender/Proofs/Trace/Families/WordMemory/ProjectedPorts.lean) derives actual pre-state reads and final writes; full native constraints place that final port in GPR space or RAM outside the ROM prefix. Ordinary/x0 ROM regressions need no shadow bytes or expected source read; dependent RAM store/load rows use the same generic transport. Native matching still includes every shadow token. These are native and cell-transfer results; original LOAD/STORE execution is checked below; physical boot/ROM binding remains open. |
| Code/ROM preservation under stores | [Initialized ROM preservation](Airbender/Review/Trace/Families/WordMemory/CodeHistory.lean) now derives equality of every byte entry below four MiB from actual projected Sail transfers and the native architectural domain. Missing bytes remain absent; successful public ROM extraction and original source/decoding evidence survive every history prefix. Public indexed setup supplies complete code windows for programs fitting that ROM region. A reversed changing SW/LW history retains both instruction words and their extracted ROM image without later-read/value premises; ordinary/x0 ROM loads retain unreadable shadow bytes and complete native matching. This does not populate Sail boot/padding bytes, bind physical exports or establish original LOAD/STORE execution. |
| Sail platform versus native RAM effects | [Public configuration preservation](Airbender/Review/Trace/Families/WordMemory/Platform.lean) derives retention of actual Machine/PMP/PMA CSRs from initialized projected transfers. [Native RAM transport](Airbender/Proofs/Trace/Families/WordMemory/MemoryTransport.lean) derives actual pre-state reads, final writes and alignment from v2 constraints/history and invokes unchanged pinned Sail translation/permission/platform proofs. The same reversed accepted SW/LW history now derives a real virtual store and subsequent virtual read of 123. Ordinary addresses exclude actual platform MMIO windows; configuration and platform interfaces remain explicit, without desired-read/result premises. Original ROM/RAM clauses are now checked separately below; complete preparation/retirement is checked below; physical boot/export remains open. No v3 implementation finding is inherited. |
| Original ROM LW versus native shadows | [Virtual transport](Airbender/Proofs/Trace/Families/WordMemory/ROMTransport.lean) derives the original memory call from public ROM bytes and actual retained source reads; native ROM bounds discharge ordinary addresses. [Original LW assembly](Airbender/Proofs/Trace/Families/WordMemory/ROMExecution.lean) connects native masked writes to the original clause, retaining original rd=x0. [Initialized ordinary/x0 regressions](Tests/WordMemoryROMTransport.lean) reach the same actual native after-state while full matching retains shadow value 123 and actual ROM bytes read 0xc0001073. Public extraction requires present bytes and does not populate absent padding. No shadow/ROM equivalence, expected read or desired-state premise is used. Original RAM clauses and row retirement are checked below; general word-memory trace composition is checked below; physical boot/export remains open. No native defect is established. |
| Original RAM LW/SW clauses | [RAM assembly](Airbender/Proofs/Trace/Families/WordMemory/RAMExecution.lean) recovers the original store operand from native port 1 and maps masked RAM-load writes to original Sail writes, including x0. Exact public decoder fields derive load/store selectors, original registers and sign extension. Unchanged original Sail virtual-memory and LW/SW clause lemmas reach actual native cell-transfer states under explicit public configuration/ordinary-address conditions. [The same reversed accepted SW/LW fixture](Tests/WordMemorySailHistory.lean) derives the intermediate state, original SW then LW results, later read 123 and actual destination write. No expected operand/read, intermediate state or desired result is supplied. Row preparation/PC retirement is now checked below; general word-memory trace composition is checked below; physical boot/export remains open. No implementation defect or v3 finding is inherited. |
| Native word-memory PC retirement | [Row assembly](Airbender/Proofs/Trace/Families/WordMemory/Execution.lean) derives native effective addresses and modular PC successors from initialized matching and public decoding. [Control transport](Airbender/Proofs/Trace/Families/WordMemory/Retirement.lean) reuses actual histories/configuration/ROM extraction through Sail nextPC preparation and tick_pc. The original dispatcher is copied without v3's LW-to-x0 deviation. Ordinary/x0 ROM fixtures reach native PC 4 with real memory reads, and reversed dependent SW/LW normal steps reach PC 8 and native terminal RAM/x3=123 without intermediate/read/prepared-state/PC-result premises. Local ordinary-RAM and actual extracted-prefix coverage conditions remain explicit. General finite trace/fetch composition is checked below; physical boot/export and cryptographic enforcement remain open; no implementation defect is established. |
| Initialized word-memory finite execution | [Public execution](Airbender/Review/Trace/Families/WordMemory/Theorems.lean) checks actual fetched bytes/original decoding and finite original LW/SW normal steps, deriving exact native terminal PC and architectural cells. Full native matching still retains independent ROM-shadow values; [the observable](Airbender/Review/Trace/Families/WordMemory/Execution.lean) selects architectural terminal tokens explicitly. Public ordinary RAM, configuration, program-in-ROM size and actual ROM-prefix seed coverage remain visible. Accepted matching derives every local address domain, row order, read, range and intermediate state. Reversed SW/LW reaches PC 8 and RAM/x3=123; ordinary/x0 ROM loads and empty traces pass. Physical boot/padding/export and cryptographic enforcement remain open. No native defect or v3 finding is inherited. |
| Fixed native zero boot | [The boot boundary](Airbender/Review/Helpers/Memory/NativeBoot.lean) uses native zero GPR/RAM/shadow tokens, PC zero/time four and the unchanged original Sail initial profile. The [short theorem](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean) derives complete original execution through the existing initialization boundary, without per-row values, reads or states. [Full native paths](Airbender/Proofs/Trace/Families/WordMemory/BootShadow.lean) keep terminal shadows zero independently of actual ROM bytes. Ordinary/x0 boot fixtures reach native PC four and actual destination values; nonzero public GPRs and invented seeds reject the fixed profile. Native runtime/replayer source hashes are pinned; Rust refinement and physical argument enforcement remain separate. |
| Proving-loader zeros versus raw-table UNIMP | V2 word padding in [the native machine helpers](../../cs/src/machine/machine_configurations/mod.rs), called by [setup padding](../../circuit_defs/setups/src/lib.rs) and [the binary loader](../../execution_utils/src/lib.rs), extends to four MiB with zero. The raw ROM table constructor uses UNIMP only beyond the image it receives. Passing a complete loader-padded image makes that fallback unreachable within ROM. [The padding model](Airbender/Review/Helpers/Tables/WordROMPadding.lean) and [symbolic proofs](Airbender/Proofs/WordMemory/ROMPadding.lean) retain input words and zero the tail without a large evaluated certificate. Existing raw-table models stay unchanged. This is a checked source/model distinction, not an implementation defect. The explicit Sail padding connection is now checked below; Rust/export refinement remains separate. |
| Explicit Sail loader padding | [The constructor](Airbender/Review/Helpers/Tables/PaddedROMImage.lean) reads the actual supplied prefix and explicitly inserts zero bytes to four MiB. [Symbolic proofs](Airbender/Proofs/WordMemory/ROMBytePadding.lean) derive exact full-ROM extraction without evaluating the huge map/list or assuming table equivalence. Prefix/outside bytes, registers, public configuration and the original zero profile survive; actual decoder setup survives under code-prefix inclusion. [Padded boot execution](Airbender/Review/Trace/Families/WordMemory/NativeBoot.lean) derives all shadow coverage and complete original execution. Ordinary/x0 native fixtures, formerly absent zero reads, exact byte boundaries and missing/oversized prefix rejection pass. General Rust/compiler/export refinement and physical argument enforcement remain open; no v3 finding is inherited. |
| Native physical setup geometry and tags | The compiled artifacts have arithmetic/word-memory widths 12/16, scalar columns 0/1, one ten-column decoder group and word-memory's four-column generic group. [Importer guards](Airbender/Import/Parse.lean) now check exact placement, all 62 offsets, native capacity and the dummy-row extent. The native table IDs are 23/24, not v3's ROM tag 34. [The active-row model](Airbender/Review/Helpers/Tables/PhysicalSetup.lean) retains dummy/zero padding and the full tagged ROM/separator regions; symbolic proofs recover exact logical membership. [The short byte-read bridge](Airbender/Review/Trace/Families/WordMemory/Setup.lean) derives actual Sail words after explicit padding. Nonempty original/padded reads, changed ROM data and wrong padding tags are checked. Native source normalizes only the reserved final setup row, which this model excludes; formal Rust/export/normalization/LDE and stage-two enforcement remain open. No implementation defect is established. |
| Actual native regional setup fixture | [The standalone exporter](../native_setup_exporter/README.md) uses actual v2 table-driver, decoder and range APIs. Exhaustive codec checks and exact regeneration retain a four-word LW/SW/x0/UNIMP input, a full zero-padded public image, all native tags/offsets and every unsupported decoder slot. [Kernel certificates](Airbender/Proofs/WordMemory/NativeSetup.lean) check complete ROM/separator/range data and decoder/image tails; actual exported ROM membership supplies original Sail byte reads after loader construction. The explicit UNIMP word remains ROM data while its decoder slot is the all-minus-one sentinel. This is expected native behavior, not a defect. General program/decoder construction, full trace padding/normalization/LDE, parsing/export refinement and argument enforcement remain open. |
| Unsupported interior decoder slots | Native preprocessing continues past unsupported words without compacting their PCs. [The sparse constructor](Airbender/Review/Helpers/Decoder/SparseSetup.lean) now retains these holes, while missing bytes/effectful decoding fail. Native mask equations reject hole/tail lookups and derive source evidence and canonical fields. [A fresh actual export](artifacts/setup/word-memory-holes-native.json) places UNIMP at PC four and supported LW/SW/x0 words at 0/8/12. [Kernel certificates](Airbender/Proofs/WordMemory/NativeSparseSetup.lean) construct actual public Sail data and check every decoder row. A complete native x0-load constraint witness at PC 12 recovers its original source. This is expected native behavior, not a vulnerability. [Sparse initialized execution](Airbender/Review/Trace/Families/WordMemory/SparseExecution.lean) now reuses the same native history, original Sail clause/retirement and terminal proofs. [A real initialized x0-load regression](Tests/SparseExecution.lean) selects actual exported slot three and derives PC 12 to 16, unchanged RAM 123 and x0 zero. Initial PC 12 is public input; no control flow skipping an executed hole is asserted. Native matching retains the actual RAM read despite x0 masking. General Rust decoder refinement, arbitrary-program export certificates and physical argument enforcement remain open. |
| Setup fidelity | [Range definitions](Airbender/Review/Helpers/Tables/Range.lean) use native Clean static tables. [Actual shared scalar data](Airbender/Review/Helpers/Tables/NativeScalarData.lean) now retains every range16/timestamp19 prefix value. The exporter calls the native range16 API and copies the pinned native timestamp clause/constant unchanged; exact clause identity and lossless reproduction pass. [Symbolic proofs](Airbender/Proofs/Tables/NativeScalars.lean) certify every prefix and source-shaped active zero filler, deriving exact original Clean lookup meanings. Filler zero is valid range data and remains in the active domain; unlike decoder sentinels, it need not be excluded. The reserved normalization row, physical multiplicities, Rust trace/LDE refinement and argument enforcement remain separate. No implementation defect is established. |
| Actual arithmetic decoder data | [The actual native export](artifacts/setup/arithmetic-native.json) preserves signed ADDI limbs, original SUB-to-x0 operands/mask, raw U-type funct3 and the indexed ADD at PC 24 after an UNIMP hole at 20. [Kernel certificates](Airbender/Proofs/AddSub/NativeSetup.lean) construct independent original Sail public data and prove every exported slot equals its sparse row. Native packed-mask equations reject holes/tail before [source recovery](Airbender/Review/Trace/Families/AddSub/NativeDecoder.lean); a complete accepted post-hole ADD witness exercises actual membership. These are confirmed native behaviors, not defects. The native family also supports custom modular MOPs, which are outside this concrete five-opcode certificate. General Rust decoder agreement, arbitrary programs and physical trace/argument refinement remain separate; sparse initialized execution is checked below. |
| Sparse initialized arithmetic | [The short execution claim](Airbender/Review/Trace/Families/AddSub/SparseExecution.lean) now composes actual sparse public construction and complete native constraints/state/memory/decoder matching through the existing arithmetic history, original Sail and terminal assembly. Constructor-derived indexed evidence stays under Proofs; the strict public statement is unchanged. [The initialized post-hole regression](Tests/SparseArithmeticExecution.lean) uses actual exported slot six and derives PC 24 to 28 and x1=246 from full aliased-port matching and original public bytes/decoding. Native equations exclude holes/tail; no public per-row read, intermediate state, desired result or table-equivalence premise is added. The UNIMP word at PC 20 remains public data; initial PC 24 does not claim a control-flow skip. General native decoder refinement, arbitrary-program certificates, custom MOPs and physical trace/argument correspondence remain open. No implementation defect is established. |
| Active decoder padding | The native setup assembler calls the same [padding API](../../cs/src/machine/ops/unrolled/decoder/mod.rs) beyond the decoder prefix; both executable paths use all-minus-one values despite a materializer comment mentioning zeros. [The direct native export](artifacts/setup/decoder-padding-native.json) and [symbolic certificate](Airbender/Proofs/Tables/NativeDecoder.lean) check the actual sentinel and all 15,728,639 extra active rows. That sentinel already occurs in each checked native prefix, so full active membership adds no query; no equivalence is assumed. Both compiled placements and active boundaries are checked. [The initialized arithmetic bridge](Airbender/Review/Trace/Families/AddSub/ActiveSetup.lean) derives the real post-hole alias execution through this full domain; native mask equations reject padding. The final normalization row, general Rust trace/LDE refinement and argument enforcement remain separate. This is confirmed native behavior and a source-comment distinction, not an implementation defect. |
| Complete active row layout | [Full row assembly](Airbender/Review/Helpers/Tables/NativeRowsData.lean) now retains actual scalar/decoder data and tagged generic tuples at imported column positions. [Projection proofs](Airbender/Proofs/Tables/NativeRows.lean) derive unchanged Clean scalar/fixed-table meanings and actual decoder membership. [Regressions](Tests/NativeRows.lean) check overlapping decoder filler/ROM regions, mixed final filler values, missing generic groups, truncated windows, scalar overflow and wrong padding tags. [Initialized arithmetic execution](Airbender/Review/Trace/Families/AddSub/PhysicalSetup.lean) uses decoder columns from the complete row and derives the real alias fixture's PC 28/x1=246. This is a source-shaped logical row/column certificate, not Rust trace/normalization/LDE or argument refinement. No defect is established. |
| Native control triples and alignment | [The complete native export](artifacts/setup/jump-control-native.json) has 65,536 cleanup rows tagged 17 and 128 separate flags/funct3/result rows tagged 43, with no added dummy row. [Certificates](Airbender/Proofs/JumpBranchSlt/ControlTables.lean) bind every actual tagged value to original Clean membership. [The native fixed-effects claim](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) derives exact key bounds/control/cleanup values from all native constraints. [An active JAL witness](Tests/JumpControl.lean) passes; altered results/out-of-domain flags and an unaligned JAL target reject. Cleanup itself retains bit one, and the native JAL equation excludes it. Public decoding is checked below; initialized original Sail execution remains open and the source terminal-PC finding is assessed below; no v2 vulnerability or copied closure premise is claimed. |
| V3 F01 retested on native v2 control rows | [Native PC bounds](Airbender/Review/Circuits/JumpBranchSlt/Theorems.lean) derive both outgoing limb ranges under explicit supported masks 1/2/4/8/16. Actual Boolean/packed equations derive selector exclusivity; outgoing high equals variable 43, consumed by scalar query index 5. [The local negative-offset row](Tests/JumpPC.lean) accepts canonical target limbs 65532/65535. Its field-minus-one high variant passes every polynomial and the other fifteen native queries, but that actual scalar query rejects it. The v3 F01 witness shape therefore does not reproduce on these native v2 rows. No terminal-PC range or verifier-closure premise is copied. Public-byte decoding is now checked below; initialized original Sail execution and full terminal-history connections remain open; no global closure result or new v2 vulnerability is claimed. |
| V2 public control metadata | [The control projection](Airbender/Review/Circuits/JumpBranchSlt/Decoder.lean) retains actual v2 SLTI/SLTIU mask 8, branch mask 16, original x0 operations and raw JAL encoding funct3. JAL -4 uses tag 7; its source v3 tag-zero convention cannot be copied. [Sparse public construction and native mask proofs](Airbender/Proofs/JumpBranchSlt/Decoder.lean) exclude every hole/tail sentinel, recover original Sail source evidence and derive mask/input/zero-flag facts before outgoing PC bounds. [Actual public-byte tests](Tests/JumpDecoder.lean) construct JAL -4, an interior UNIMP hole and original SLTIU-to-x0 at PC 8. The full native tag-seven JAL passes; the earlier locally valid tag-zero query is rejected by public membership. A malformed high-PC variant keeps actual public membership and all polynomials but fails the native range query. This closes the local logical decoder boundary, without a mask/range/desired-result or closure premise. Actual native program export is certified below for this input; general Rust decoder refinement, initialized original control execution and terminal matching remain open. These are native behavior differences, not a new vulnerability. |
| Actual native control decoder data | [The actual signed native export](artifacts/setup/jump-decoder-native.json) confirms raw JAL -4 funct3 7, the unsupported PC-four hole and original SLTIU-to-x0 mask 8/zero flag 1 at PC eight. [Independent Sail certificates](Airbender/Proofs/JumpBranchSlt/NativeSetup.lean) check every prefix and tail row. The short source/PC claim consumes actual exported membership with all native constraints; its full JAL witness passes, while the prior local tag-zero query fails. Separate arithmetic/control importer profiles reject crossed or unsigned-only data. These are confirmed native behaviors, not implementation defects. Arbitrary-program Rust decoder refinement, initialized original control execution, terminal matching and physical argument enforcement remain separate. |
| Native control readonly aliases | [Actual native clock extraction](Airbender/Proofs/JumpBranchSlt/Timestamp.lean) proves the shared clock contract from control-specific equation/query indices and imported ports. [Public initialized history](Airbender/Review/Trace/Families/JumpBranchSlt/History.lean) derives complete Clean consistency and newest reads from actual Sail seeds/PC and full native matching. [The full JAL -4 fixture](Tests/ControlHistory.lean) retains two x0 reads and the actual x1 link write; the second x0 read consumes the first readonly refresh. Its stale variant passes every local native constraint but fails logical memory matching. This confirms the existing argument boundary, not a v2 implementation defect. The lower 19-bit clock carry is accepted with correct high limb; explicit missing-register data rejects public initialization. Control word/write bounds and Sail cell transfers are checked below; original instruction execution and terminal instruction-state matching remain separate. |
| Native control masked writes and Sail cells | [Write equations](Airbender/Proofs/JumpBranchSlt/Writes.lean) derive actual destination bounds from one-hot selection, ranged jump links and the native one-bit comparison result. Full public decoding supplies masks/zero flags, while initialized induction derives all native read/write/terminal ranges. [x0 and cell realization](Airbender/Review/Trace/Families/JumpBranchSlt/SailHistory.lean) derive every zero-register write and clock-ordered Sail cell transfer from actual masks and complete matching. [The exported-JAL regression](Tests/ControlValues.lean) retains both x0 refreshes and replaces old x1=123 with link four. A malformed zero flag two passes every local native equation/query and yields an unbounded destination, while full decoder membership rejects it. This confirms the explicit external lookup boundary; no accepted-trace defect is established. Original control instructions, terminal instruction-state matching, physical boot and Rust/cryptographic refinement remain open. |
| Native control instruction pre-state reads | [Readonly-prefix transport](Airbender/Proofs/Trace/Families/JumpBranchSlt/PortReads.lean) now binds original decoded GPR reads/writes to actual imported control ports. [Initialized register histories](Airbender/Review/Trace/Families/JumpBranchSlt/Registers.lean) construct all segment states from native clocks/matching and original public decoding: both source reads and the old destination read use the same cell-history pre-state, including aliases. [The exported-JAL regression](Tests/ControlRegisters.lean) derives both x0 reads, old x1=123 and link write four through this claim. No supplied read, segment state, schedule or desired write is used. This is a checked native connection, with no new implementation defect. Original control operation semantics/clauses, PC retirement and terminal instruction-state matching remain open. |
| Native JAL/JALR saved PC+4 | [Native equations and shared modular addition](Airbender/Proofs/JumpBranchSlt/Link.lean) now derive the actual masked link write. Full public decoding supplies both PC limb bounds and the exact x0 flag; native jump masks recover operation selectors. Actual scalar queries zero/one range the saved word, while Boolean assertions 9/5 constrain carries 49/28. [Regressions](Tests/JumpLink.lean) check the exported negative-JAL link, logical odd-source JALR, original JAL-to-x0 with retained raw link twelve, all native constraints for unmasked PC+4 wrap to zero, and altered-link rejection. The wrap case is local, not an initialized/public-decoder trace; the new logical words have no new general native export certificate. No v2 defect or copied terminal-closure assumption is established. Jump targets, comparison/branch semantics, original Sail clauses/retirement and Rust/cryptographic refinement remain separate. |
| Native initialized JAL/JALR targets | [Native arithmetic and cleanup](Airbender/Proofs/JumpBranchSlt/Target.lean) derive both target limbs and alignment from actual v2 equations, carry assertions and range/fixed queries. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Targets.lean) derives source bounds through complete native matching and PC/immediate bounds, JAL parity and selectors through original public bytes. The actual candidate-high range removes the source v3 closure premise. [Regressions](Tests/JumpTarget.lean) cover exported negative JAL, initialized aliasing JALR from public x1=257 to target 264, local x0/wrap targets and bit-one rejection despite valid cleanup. No new v2 defect is established; the logical JALR fixture has no new native export certificate, and local wrap is not initialized execution. Original Sail instruction/retirement, comparisons/branches and full terminal instruction-state matching remain open. |
| Native initialized comparison results | [Numerical proofs](Airbender/Proofs/JumpBranchSlt/Comparison.lean) preserve native positive flags 31/33, derive signs from shifted-limb equations and actual scalar bounds, reuse original subtraction/borrow lifting and unchanged signed word ordering, then apply the actual conditional table and masked writes. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Comparisons.lean) derives operand ranges from full matching and selectors/signedness/x0 from actual original public decoding. [Four initialized cases](Tests/ControlComparisons.lean) distinguish signed/unsigned -1 versus one and positive 123 versus sign-extended -1, including true SLTIU-to-x0 with a retained readonly refresh and discarded raw one. Its query matches the prior actual native export. A flipped positive flag preserves its field equation only with an out-of-range shifted limb; actual scalar query two rejects it. No v2 defect is established. Logical-program native export, branch semantics, original instruction/PC execution and full terminal instruction-state matching remain separate. |
| Native comparison PC routing | [Actual native equations](Airbender/Proofs/JumpBranchSlt/ComparisonPC.lean) route comparison candidate 42/43 directly to final PC 13/14. Scalar queries four/five derive both limb ranges, Boolean carries retain RV32 wrap, and unchanged modular addition proves PC+4. [The short public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonPC.lean) obtains incoming bounds/alignment and selectors from original public decoding without a register-image boundary or final-high closure assumption. [Tests](Tests/ComparisonPC.lean) reuse all four initialized comparisons, check full native local wrap and reject altered PC. This is confirmed native behavior, not a defect. Local wrap does not claim initialized execution/new native export; original Sail retirement, branch semantics and complete terminal instruction-state matching remain open. |
| Native initialized branch flags | [Subtraction and inverse proofs](Airbender/Proofs/JumpBranchSlt/Branch.lean) derive unsigned borrow, exact operand equality and native positive flags before the actual conditional lookup resolves all six branch conditions. Actual routing bits are complementary and unused destination writes are zero independently of the external x0 flag. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/Branches.lean) obtains operand ranges from full matching and exact mask/tags from original public decoding. [Eighteen cases](Tests/Branches.lean) check both outcomes for every opcode, equality and opposite signed/unsigned orderings, retaining the real zero write event. A false equality flag/BEQ answer passes the actual conditional table but fails native inverse equation 16. This confirms enforcement, not a defect. New logical-program native export, branch targets, original Sail retirement and full terminal instruction-state matching remain separate. |
| Native branch PC selection/alignment | [Branch PC calculations](Airbender/Proofs/JumpBranchSlt/BranchPC.lean) derive PC+offset when taken and PC+4 otherwise from actual candidate, carry and routing equations. Both scalar queries bound the output, removing the source final-high premise. Untaken rows use the raw candidate; taken rows use cleanup, while original decoded parity and native assertion 26 exclude low-bit changes. [The initialized claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchTargets.lean) reuses the checked six conditions and derives all local PC/offset facts from original public bytes. [Tests](Tests/BranchTargets.lean) reuse eighteen initialized cases and check full local negative/taken-wrap/untaken-wrap rows. An ignored untaken offset two is accepted; taken offset two has valid cleanup but fails the bit-one assertion. This confirms native enforcement, not a defect. Local wrap/negative rows are not initialized/public-decoder execution or new exports; original Sail retirement and full terminal instruction-state matching remain separate. |
| Native comparisons versus original Sail retirement | [The native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) reuses checked comparison results, actual same-pre-state register reads and masked writes, exact public constructors/sign extension and unchanged preparation/retirement. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/ComparisonExecution.lean) constructs every history segment and retires its original clause to the native PC. [All four initialized cases](Tests/ComparisonExecution.lean) pass from actual public states; true SLTIU-to-x0 retains source x1=123, stutters in data and retires PC eight to twelve. The source nonzero-rd restriction and final-high closure interface are not carried into this v2 claim. No defect is established. General fetched trace/terminal instruction-state composition, jump/branch CSR clauses and new program-export certificates remain open. |
| Original branches and public ISA state | [The checked native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/BranchExecution.lean) derives original six-opcode conditions, actual source reads, sign extension and exact aligned native targets before invoking original BTYPE preparation/retirement. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/BranchExecution.lean) constructs segment states and explicitly requires an actual initial misa entry, with arbitrary value. Unchanged original CSR frame lemmas transport that entry; the copied Sail control-flow module preserves its real read even on an aligned taken path. [All eighteen native fixtures](Tests/BranchExecution.lean) execute unchanged with only that public CSR entry added, deriving complete data stuttering and targets. Old partial states have no entry and their original accessor cannot succeed. This is a public-state boundary, not a v2 defect or a claimed whole missing-CSR branch exception trace. Original jump CSR effects and full fetched control/terminal instruction-state composition remain open. |
| Original jumps and landing-pad profile | [The native connection](Airbender/Proofs/Trace/Families/JumpBranchSlt/JumpExecution.lean) reuses exact native links/targets, original metadata and same-pre-state reads/writes, then invokes the unchanged original retirement declaration. [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/JumpExecution.lean) constructs segments and retains actual initial misa readability plus Machine/MLPE-clear security data only when JALR occurs. Unchanged history frames derive all row CSR reads. [Regressions](Tests/JumpExecution.lean) reuse negative exported JAL and logical aliasing JALR, deriving original retirement and actual link writes with the same after-state. JAL has no privilege/security entries; the old partial JALR state cannot supply its original privilege read. This is an explicit original-Sail platform boundary, not a native defect, whole missing-CSR exception trace or new export certificate. Full fetched control/terminal instruction-state composition remains open. |
| Artifact fidelity | [Importer](Airbender/Import/Parse.lean) checks consumed addresses, residue bounds and unsupported features. Hashes pin the inputs; parsing/emission and native metadata interpretation are not formally proved. |
| Complete fetched control execution | [The public claim](Airbender/Review/Trace/Families/JumpBranchSlt/Execution.lean) composes all twelve supported original control constructors using unchanged shared fetch/retirement assembly. Native GPR history preserves public bytes; accepted state/memory matching derives actual order, intermediate states and terminal PC/register reads. Actual scalar candidate queries derive raw terminal PC bounds, including empty traces, without a copied closure premise. Initial misa and conditional JALR Machine/MLPE-clear CSR profile remain explicit. [Existing jump/branch/empty cases](Tests/ControlExecution.lean) and [reversed dependent JAL/JALR](Tests/ControlSequence.lean) pass. The stale-link variant passes all local constraints, public decoding and state matching but fails actual native memory matching. No native defect or new Rust program-export certificate is claimed; whole-machine/protocol/init/teardown and general refinement remain separate. |
| Unsigned mul/div native artifact and byte ranges | [The import](Airbender/Review/Circuits/MulDiv/Artifact.lean) retains all 49 equations and 20 lookups, including six exact paired-byte queries covering eleven native byte columns with odd-column zero padding. [Symbolic certificates](Airbender/Proofs/MulDiv/SmallRange.lean) identify all 65,536 actual exported tagged rows and exact Clean membership; [bounds](Airbender/Proofs/MulDiv/ByteBounds.lean) follow from native queries without supplied ranges. Two native optimized-out variables are scratch metadata only; consuming them as equation/query inputs, overflow/aliasing, malformed pairing/padding and changed table geometry are rejected. Endpoint/overflow/padding/tag regressions pass. This is a checked importer/data boundary, not MUL/DIV instruction correctness, a native defect or inherited v3 coverage. Numerical arithmetic is checked below; public decoding/history and original Sail execution remain open. |
| Native unsigned mul/div arithmetic and discarded writes | [The public local claim](Airbender/Review/Circuits/MulDiv/Theorems.lean) checks MUL/MULHU/DIVU/REMU selected results and actual masked writes. The unchanged shared integer product lemma is connected to native explicit bytes and split carries; accepted constraints derive every intermediate/output bound. [Native division](Airbender/Proofs/MulDiv/Division.lean) uses Mersenne31 inverse 32768, not the source -30720, and derives strict remainder bounds and zero-divisor all-ones quotient/dividend remainder from actual equations. Packed masks are 2/0/3/1 independently of x0. Forty full native assignments cover boundary and discarded-write cases; corruption of actual writes is rejected. This establishes local numerical correctness under explicit packed operation, input limb-bound and destination-zero interfaces, not original public decoding/history/Sail execution or a new native Rust export. No v2 defect is established. |

| Stateful MUL/DIV decoding and initialized numerical interfaces | [The initialized claim](Airbender/Review/Trace/Families/MulDiv/Theorems.lean) derives all numerical inputs from actual public bytes, seed/PC reads and accepted native matching. The original decoder reads misa.M, so a pure-only constructor cannot cover these forms. [Stateful setup](Airbender/Review/Helpers/Decoder/StatefulSetup.lean) preserves the real read and rejects decoder errors; the unchanged shared frame proof preserves state/misa replay. Sixteen nonempty initialized traces cover all four operations, zero divisors and actual x0 writes. Disabling M rejects actual original decoding; locally valid wrong tags and compensating flag-2 writes fail full public membership. This is a checked configuration/argument boundary, not a native defect. Original operation execution/retirement, physical boot/export and cryptographic enforcement remain open. |

| Actual MUL/DIV Sail GPR histories and decoder replay | [The public claim](Airbender/Review/Trace/Families/MulDiv/Registers.lean) constructs all segment states and original same-pre-state register reads/actual masked writes from native matching and public initialization. Native x0 equations retain original discarded opcodes. Actual GPR histories preserve code and misa, so the original stateful decoder replays after real updates. Sixteen initialized cases and a two-MUL source/destination alias sequence pass; the stale old-destination timestamp passes local constraints/decoding/state matching but fails native memory matching. This is a checked logical argument/configuration boundary, not a native defect or full MUL/DIV instruction/PC execution. |

| Original local MUL/DIV execution and native PC wrap | [The public instruction-history claim](Airbender/Review/Trace/Families/MulDiv/Execution.lean) derives original four-operation clauses, actual masked writes and original preparation/retirement from constructed native histories. Actual carry/inverse gates derive bounded modular RV32 PC+4; a full imported row wraps 0xfffffffc to zero. Sixteen initialized cases retain zero divisors and x0 retirement; the actual aliased second MUL retires PC four to eight after a real update. Complete fetched stateful-decoder composition remains unfinished; no native defect, fetched wraparound program or compiler refinement is claimed. |

| Complete fetched unsigned MUL/DIV execution | [The public theorem](Airbender/Review/Trace/Families/MulDiv/FetchedExecution.lean) derives finite original Sail fetch/stateful decoding/preparation/retirement from public initialization and full native matching, including actual terminal PC/register reads and bounds. Actual misa/code frames supply replay; no pure-decoder, extra ISA-read, per-row-step or desired-state premise is supplied. Sixteen complete cases, zero divisors/x0, concrete arithmetic results, a reversed two-MUL alias sequence reaching PC eight/x1=x3=861 and empty execution pass. This closes the family execution connection; no native defect, fetched wraparound fixture, new Rust export or cryptographic/compiler refinement is claimed. |

| Native shift/binop decoder migration differences | [The actual native export](artifacts/setup/shift-decoder-native.json) retains original x0 destinations, full sign-extended 16-bit immediate limbs and SRAI encoded funct7 (shift 31 gives 1055); native masks/tags differ from v3. [Independent original Sail proofs](Airbender/Review/Trace/Families/ShiftBinop/NativeDecoder.lean) connect all twelve ordinary forms, their x0 variants, the unsupported ADD hole and every exported row. Actual Rust runs reproduce empty-CSR filtering and unsupported REV8/rotate/illegal RV32 shift rejection. These are profile differences, not a native defect. This finite decoder-data certificate supplies no shift/binop constraint/execution coverage; dynamic table import/membership and custom CSR/oracle semantics remain separate. |

| Native zero and binary table membership | [The actual native prefix](artifacts/setup/shift-binary-native.json) retains zero and XOR/OR/AND IDs 0/4/6/7 with compiled offsets 0/1/65537/131073. [Public helper claims](Airbender/Review/Helpers/Tables/NativeBinary.lean) connect original Clean membership to every actual native binary row and derive both byte bounds and exact bitwise results. Source literal-block certificates check all 196,608 outputs; symbolic geometry retains actual keys/tags and the zero row. Byte 256 and a changed XOR output reject. An evaluated geometry check hit Lean allocation cap; splitting source-shaped structural geometry resolved it with unchanged ceilings. This is a certified table prerequisite, not shift/binop circuit/execution or general compiler/cryptographic soundness. Large shifts and custom CSR/oracle behavior remain separate; no native defect is established. |

| Native truncation, padding and sign-fill tables | [Actual selected native rows](artifacts/setup/shift-scalars-native.json) retain IDs 47/52/53 and compiled offsets 200705/8654849/10752001 across unexported regions. [Public helper results](Airbender/Review/Helpers/Tables/NativeShiftScalars.lean) derive bounds, truncation, padding and the exact RV32 mask for every row, including all 2,097,152 sign-fill entries. Shift zero fills no bits even for a negative high limb; one/sixteen/31 and positive-boundary fixtures pass. Nonzero padding, changed truncation/sign-fill and oversized keys reject. The combined upper-mask calculation reached the resident ceiling; four independent 16-domain certificates retain fixed caps. Four logical-shift tables and dynamic circuit/execution coverage remain separate; this is supported native behavior, not a defect. |

| Native low-input SRL table | [All actual native rows](artifacts/setup/shift-srl-low-native.json) retain ID 50 and compiled offset 4460545. [Public membership/results](Airbender/Review/Helpers/Tables/NativeSrlLow.lean) derive key/output bounds, zero high output and exact zero-extended RV32 logical shift for all 2,097,152 rows. Six symbolic native-block certificates use unchanged getters and the source block-check framework over all 74 stored blocks. Final-bit and shift-zero/one/fifteen/sixteen/31 fixtures pass; changed outputs, nonzero high padding and oversized packed keys reject. The other three logical-shift tables and full dynamic circuit/execution connection remain separate; no native defect is established. |

| Native high-input SLL table | [All actual native rows](artifacts/setup/shift-sll-high-native.json) retain ID 49 and compiled offset 2363393. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSllHigh.lean) derive packed-key/output bounds, zero low output and exact wrapped RV32 high-limb shift for every row. Six symbolic partitions retain 74 actual blocks; ten actual templates have structural geometry and 64-query kernel certificates. Generic size/output assembly avoids imported-array normalization after controlled resident/allocation-limit failures, with no surviving owned workers or raised ceilings. Top-bit loss, the final surviving bit, shift sixteen/31 and malformed queries pass. Discarded bits match RV32; no native defect is established. Low-input SLL, high-input SRL and full dynamic circuit/execution coverage remain separate. |

| Native low-input SLL table | [All 2,097,152 actual rows](artifacts/setup/shift-sll-low-native.json) retain ID 48 and compiled offset 266241. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSllLow.lean) derive packed-key/both-limb bounds and exact reconstructed RV32 logical-left shifts. Checked reuse identifies the full low-output column and 73 high-output blocks with previously certified native SLL-high data; six symbolic prefix partitions cover actual carry values. First-carry, shift-sixteen, final-bit/discard and malformed limb/result/key regressions pass under unchanged caps. Carry and bit discard match RV32; no native defect is established. High-input SRL and the dynamic circuit/execution connection remain separate. |

| Native high-input SRL table | [All 2,097,152 actual rows](artifacts/setup/shift-srl-high-native.json) retain ID 51 and offset 6557697. [Two public helper claims](Airbender/Review/Helpers/Tables/NativeSrlHigh.lean) derive packed-key/both-limb bounds and reconstructed RV32 right shifts. The high column and 73 low-output blocks reuse native SRL-low. All 146 native low-output blocks retain rotated templates, the 65,537-row initial zero block and shortened shift-eleven affine block; bounded stored-template and symbolic certificates prove exact values. Cross-shift/reset, shift-sixteen/31, final-bit and malformed-query regressions pass under unchanged caps. All four logical-shift limb tables now have helper membership/results; no native defect is established. Dynamic circuit import and initialized shift/binop execution remain separate. |
| Compiled shift/binop dynamic selectors and CSR profile | [The native import](Airbender/Review/Circuits/ShiftBinop/Artifact.lean) retains all fifty equations, eight timestamp queries and four physical selector witnesses as evaluated fourth Clean fields. [All twelve actual regions](Airbender/Review/Circuits/ShiftBinop/Tables/Native.lean) retain 10,817,537 tagged rows; [structural proofs](Airbender/Proofs/ShiftBinop/NativeLookup.lean) include every stored native row. The separately configured CSR region uses the exact compilation-test generator (nondeterminism enabled, empty delegation list), ID 25/offset 196609/4096 rows. Native source explicitly requires separately configured proving/setup CSR contents. This is an import/configuration boundary, not a runtime CSR binding, custom CSR/delegation execution claim or native defect. [Regressions](Tests/ShiftArtifact.lean) retain selectors, metadata, the native zero row and actual CSR data; malformed/crossed profile, mapping and offset cases reject. Numerical and initialized shift/binop execution remain open. |

| Accepted native tagged-lookup resolution | [Short native lookup claims](Airbender/Review/Circuits/ShiftBinop/Lookups.lean) extract all four queries and canonical selectors directly from original Clean acceptance. An exhaustive structural partition proves unique tags for all twelve actual regions; selected membership resolves to the existing binary/scalar/four logical-shift helper results with no equivalence premise. Tag zero requires three zero fields; it is not a wildcard. [Regressions](Tests/ShiftLookups.lean) reject wrong results, crossed/unsupported selectors and nonzero inactive data, while retaining boundary rows and canonical field wraparound. This establishes the native lookup connection, not operation routing, numerical circuit soundness or initialized Sail execution. The compilation CSR fixture remains separate from runtime CSR setup/custom instruction semantics. No native defect is established. |

| Decoded native shift/binop routing | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Routing.lean) derives all four table tags, register/immediate operand selection and zero ordinary request multiplicity from original public bytes, native decoder membership and native constraints. Six Boolean bits bound the mask to 63 and exclude sentinel decoder rows. Native SRA uses sign fill before its two logical contributions; SRAI retains its encoded funct7 payload. [Complete row regressions](Tests/ShiftRouting.lean) cover twelve ordinary forms and every x0 variant, with 96 exact native lookup certificates and wrong-tag/operand/CSR-bit rejection. Numerical word results, initialized Sail register/history execution, runtime CSR binding and worker/request protocol enforcement remain separate. This is checked v2 routing, not a native implementation defect. |

| Native binary numerical results | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Binary.lean) derives exact XOR/OR/AND selected RV32 words and actual decoded x0-masked writes from original public bytes, native decoder membership and accepted native constraints. The four byte lookups derive both operand bounds; native inverse-256 equations reconstruct all six input/output limbs. Full word values above Mersenne31 remain intact. [Twelve binary native cases](Tests/ShiftBinary.lean) cover register/immediate/x0 forms, negative immediates and rejected corrupted reconstruction/selected limbs/x0 writes. Native shift arithmetic, initialized register/history transport and original Sail instruction execution remain unfinished. No native implementation defect is established. |

| Native shift contributions | [The short public claim](Airbender/Review/Circuits/ShiftBinop/Shifts.lean) derives low-five-bit truncation, exact canonical packed-key SLL/SRL/sign-fill contributions and actual selected-word assembly from original public bytes, native decoder membership and accepted constraints. Native source/amount field equations, all contribution bounds and literal inactive zero slots are retained. SRA uses sign fill before low/high logical contributions. [Twelve complete native cases](Tests/ShiftContributions.lean) retain SRAI 1055→31, shift-31/x0 boundaries and corrupt key/inactive/missing-fill rejection. Binding packed keys to initialized bounded source reads, canonical selected limbs and architectural shift/Sail execution remains unfinished. This is a checked native contribution connection, not a native defect or a substitute source-bound premise. |

| Native shift/binop initialized history and x0 aliases | [The short public history claim](Airbender/Review/Trace/Families/ShiftBinop/History.lean) connects actual public Sail seeds/PC and native matching to complete Clean history and latest reads for all three native ports. Actual carry/borrow equations and eight timestamp queries derive all row/prior bounds, alignment, four-tick advancement and port order. [Twenty-four complete initialized fixtures](Tests/ShiftHistoryFixture.lean) pass with actual masked writes; six immediate/x0 aliases consume the earlier readonly refresh at time five. Their stale alternatives pass local native constraints but fail full memory matching. This confirms necessary global matching behavior, not a native implementation defect. Source-word bounds, canonical packed-key binding, Sail cell/instruction execution and runtime CSR binding remain separate. |
