# Verification status

**Checked** means kernel-checked claims over imported v2 native constraints
and logical matching under the explicit Review interfaces. See [trust boundaries](TRUST_AND_REVIEW.md)
and the [backport plan](FORMAL_VERIFICATION_PLAN.md). V3 results are source material,
not completed v2 coverage.

## Checked coverage

| Circuit | Coverage |
| --- | --- |
| [ADD/SUB](Airbender/Review/Circuits/AddSub/Theorems.lean) | Conditional ADD/ADDI/SUB/LUI/AUIPC destination and original Sail PC/register effects. Packed native masks derive the eight selector bits. The actual masked destination write is observed. Aligned PC wraparound and discarded x0 writes are included. |

| Integration | Coverage |
| --- | --- |
| V2 artifact import | All 34 quadratic and 3 linear equations, four 16-bit and eight 19-bit timestamp queries from the pinned ADD/SUB layout. Bounds/placement guards and both native zero coefficient encodings. |
| Reused foundation | Unchanged property definitions, word representation/arithmetic and pinned Sail reference/execution lemmas. Source hashes are checked. |
| Native state/port clocks | Typed physical state and three direct ports, including actual destination writes. Four-tick advancement and strict previous-write/port order follow from imported equations/queries under initial/prior clock bounds and alignment. The initialized-history layer now derives these local inputs from matching and initial boundaries. |
| Initialized logical memory | Accepted native state/memory matching, initial clock bounds/alignment and unique seed addresses construct complete Clean online consistency, per-address paths and newest preceding reads. Readonly refreshes and actual destination writes are included. Public Sail seed/initial-PC construction is checked separately below. |
| Public initial image | Actual Sail register/RAM and PC reads construct native seed tokens and initial PC at native clock four. Missing registers/bytes reject construction. Seed word/clock bounds and address uniqueness follow; no per-row values or clocks are supplied. Physical boot/profile remains separate. |
| Native decoder placement | Ten-column v2 query order, separate rd-zero flag, packed mask and actual memory/witness bank placement are imported and mechanically checked. Unsupported extra descriptor fields fail closed. Selected-profile construction and logical membership are checked below; generation/export remains separate. |
| Public decoder setup | Actual public bytes and pinned Sail decoding construct selected five-opcode rows at PCs 4*i with power-of-two capacity and the complete native-shaped minus-one tail. Missing/unsupported/effectful entries fail. Native packed-mask equations exclude padding before logical membership recovers public source evidence, zero flags and canonical PC/immediate words. Rust generation/export fidelity remains separate. |
| Initialized native word bounds | Public Sail seeds, accepted matching/clocks and complete decoder membership derive every native read, actual masked write and terminal word bound. No per-row bounds or flag answers are supplied. |
| Native-to-Sail history | Public seeds, native matching and complete decoder membership derive actual Sail cell reads/writes and all intermediate states. Native masked writes preserve x0 without v3 NOP preprocessing. Public RAM-cell alignment supplies disjoint byte windows. Native clocks derive row ordering/grouping and readonly refreshes stutter even with aliases; decoder indices identify actual Sail GPR reads/writes. Instruction execution remains separate. |
| Native PC path | Successful public setup retains its indexed PCs and derives every incoming bound/alignment through RV32 truncation. Native carry/wrap equations derive bounded outgoing successors; state matching and the actual public initial PC bound the terminal PC, including empty traces. No per-row PC premise is supplied. Actual Sail retirement remains separate. |
| Decoded arithmetic row retirement | Proof-layer assembly derives mask/zero flag, preprocessing, operand/immediate bounds, original Sail reads, PC facts and native observable mapping for all five arithmetic opcodes. Original Sail normal preparation/execution/retirement reaches the actual masked native write. Control-register commutation supplies rebased PC reads. No erased-source or per-row numerical premise is added to the initialized assembly. Complete trace composition is checked below. |
| Initialized arithmetic execution | Public Sail state and selected five-opcode setup, accepted native constraints/state/memory matching and public RAM alignment derive a finite original Sail normal-path trace to exact terminal PC/register/RAM values. All row order, reads, bounds, selectors, preprocessing, intermediate states and retirement effects are proved. Actual code-byte reads and pure original decoding are preserved across native GPR updates; empty traces are included. Physical setup/argument enforcement remains separate. |
| [Word-memory native transfers](Airbender/Review/Circuits/WordMemory/Theorems.lean) | All 31 quadratic/four linear equations, two scalar/eight timestamp queries and both fixed three-column ROM queries are imported. Three native ports and all decoder columns are checked. Complete native-shaped separator/ROM tables derive canonical aligned address limbs, exact ROM data, mixed port selection, masked RAM/ROM loads and RAM-only stores. The native Mersenne31 source-plus-immediate address calculation derives both carries and RV32 wraparound from explicit source/immediate bounds. PC bounds/alignment and native clock inputs yield modular PC successors, four-tick advancement and strict port order. Public decoding and initialized logical history/ranges are checked below; actual intermediate Sail reads, boot/padding/shadow projection and instruction execution remain subsequent milestones. |
| [Word-memory public decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean) | A separate checked native registry and original public LW/SW bytes construct complete padded setup. The native Boolean store mask rejects padding before membership recovers actual Sail source evidence, exact rd-zero flags, canonical register indices, immediate/PC bounds and incoming alignment. Sign extension and original x0 loads are retained. Logical read ranges/history are checked below; actual intermediate Sail reads, boot/padding/shadow-state binding and instruction execution remain open. |
| [Public ROM image/read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) | Original Sail byte reads construct a length-preserving ROM vector; excessive counts and missing bytes fail. Native table data is recovered as an actual Sail read inside the extracted prefix. A complete 1048576-word extraction derives coverage of every native ROM address. Full native UNIMP padding is retained; no expected-read/table-equivalence premise is supplied. Supplying Sail boot/padding/shadow state and proving physical setup/export remain separate. |
| [Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean) | The native clock instance reuses shared matched-clock recovery and complete Clean history/latest-read proofs for every native port. Actual public seed/PC reads discharge initial clocks, ranges and unique addresses; no per-row clock/read/order premise is supplied. Readonly ROM-shadow accesses remain participating native accesses. Their architectural projection remains separate. |
| [Word-memory value ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean) | Native load/store/mask equations preserve word bounds through earlier port copies or canonical ROM data. Full padded decoder membership recovers the zero flag. The unchanged shared decreasing-time induction derives every read, actual write and terminal word bound from actual public seeds and matching, including discarded shadow reads and x0-masked writes. Actual intermediate Sail reads/execution remain separate. |
| Range tables | Native Clean static-table definitions with explicit range semantics; v2 setup-generator binding is pending. |

## Remaining work

- Bind physical Rust decoder/setup exports and expand mixed/custom programs.
- Extend initialized execution to native word-memory, jump/branch/SLT and the remaining supported families; preserve each native metadata and argument boundary.
- Backport the remaining ordinary circuit families, worker operations, unified machine, full traces and initialization/teardown.
- Retest v3 findings against v2 before carrying over counterexamples or temporary assumptions.
- Prove the deferred import/compiler/cryptographic connections under a separately scoped claim.

No whole-machine or cryptographic soundness is claimed. Completeness is defined
but unproved. Unsupported fixed tables/dynamic selectors, byte ranges and inter-row linkage
are rejected rather than omitted from the local importer target.

## Validation

Current checked checkpoint:

- Library, both CLI entrypoints and all fourteen concrete test modules pass.
- Importer regressions: 46 checks pass.
- Axiom audit: 361 explicit roots; only propext, Classical.choice and Quot.sound.
- All seventeen public Review theorems (four circuit claims, eleven trace claims and two reused port-representation lemmas) have explicit axiom roots; guide references, links and layering checks pass.
- Source provenance: 59 unchanged reused files, two native circuit artifacts and nineteen native Rust sources.
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
- No handwritten project warnings, admitted proofs or project axioms.
- Serial bounded gates pass; parent/child timeout and memory probes confirm termination with no live owned processes.

Run the [reproduction commands](README.md#reproduce) for the current checkpoint.
