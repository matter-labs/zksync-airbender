# Trust and review boundaries

## Review entry points

Start with [Properties](Airbender/Review/Helpers/Properties.lean), then the short
[ADD/SUB theorems](Airbender/Review/Circuits/AddSub/Theorems.lean) and their
[Model](Airbender/Review/Circuits/AddSub/Model.lean). The local theorem takes
explicit decoded-input interfaces; it is not an initialized whole-run claim.
The separate short [trace memory theorem](Airbender/Review/Trace/History.lean)
constructs complete Clean memory history and latest reads from native logical
matching and explicit initialization tokens. The
[public-image theorem](Airbender/Review/Trace/Initialization.lean) obtains those
tokens and the initial PC from actual Sail reads of a supplied state/domain.

## Sources and pins

The target is dev revision 67ee094449abaebc77e58435f130ce6ea27721e5. The source
formalization is revision 805909325; [provenance](artifacts/provenance.json)
records its full commit and byte-identical shared modules, generated references,
native Rust source hashes and the v2 JSON identity. Lean, Mathlib, Clean and
lean-sail versions are unchanged. The [Clean preparation](scripts/prepare_clean.py)
is the existing guarded compatibility patch, not a change to its semantics.
The [Sail generation record](generated/sail-rv32/provenance.json) is copied unchanged.

## Import and generation fidelity

Mersenne31 coefficients are non-Montgomery residues in 0..=2147483647; the upper
endpoint is another representation of zero. The [coefficient lemma](Airbender/Import/Coefficients.lean)
proves signed interpretation in the native characteristic. Other generic prime
instances interpret those same signed equations and are not additional native artifacts.

[Native clock/port import](Airbender/Import/Parse.lean) checks two-limb group
extents, physical banks, consecutive port slots and query/borrow counts. Emitted
metadata is pinned by [mechanical bindings](Airbender/Proofs/AddSub/ArtifactChecks.lean).
The [clock proof](Airbender/Proofs/AddSub/Timestamp.lean) derives advancement and
strict access order under local initial/prior clock bounds and alignment.
The [initialized history layer](Airbender/Proofs/Trace/History.lean) discharges
those per-row inputs from logical state/memory matching and public initial clock
bounds. The v2 carry equations need no source-field inverse constant.

[Decoder placement](Airbender/Review/Helpers/Decoder/README.md) now resolves all
ten v2 query columns, including the decoder-owned zero flag and packed mask.
Group extents and memory/witness bank choices are checked; extra unconsumed
funct7/family descriptor fields fail closed. This is metadata interpretation,
separate from the [public selected-profile setup constructor](Airbender/Review/Helpers/Decoder/Setup.lean).
The constructor reads public bytes and original Sail decoding at native PCs 4*i,
retains a power-of-two capacity and the full all-minus-one tail, and rejects
missing/unsupported/effectful entries. It covers the selected five arithmetic
instructions. General Rust generation/export correspondence remains unproved;
no physical exported setup artifact or mixed/custom-opcode coverage is claimed.
Logical membership is explicit over the complete table, with no table-equivalence
premise. Native packed-mask equations exclude padding and recover actual decoded
source evidence, the zero flag and canonical decoder PC/immediate words. The v2 decoder
retains original opcode masks/operands for x0, unlike the source's NOP projection;
the local interface and a nonzero-operand SUB-to-x0 regression now preserve that.

The [schema](Airbender/Import/Schema.lean) is the consumed local-row projection of
the v2 compiled artifact. All linear/quadratic equations and scalar/timestamp
queries are emitted as native Clean operations. Only the two native word-memory
fixed tables are supported, with exactly three columns. Unknown tables, dynamic selectors, malformed arities, byte ranges and
state linkage fail closed. Native stage-two arguments,
public boundary conditions, decoder tables and memory matching are not implied
by this projection. Their remaining work is explicit in the status and plan.

Logical variable IDs are recovered uniquely from physical column placement.
The [named mapping](Airbender/Review/Circuits/AddSub/Model.lean) exposes actual
destination-write variables 37/38 rather than raw arithmetic variables 29/30.
The proof connects both using the imported x0 mask equations. Pinning and parser
regressions check parts of this connection; formal parsing/emission fidelity is
not proved.

The separate [word-memory checkpoint](Airbender/Review/Circuits/WordMemory/Theorems.lean)
imports every native equation/query and all mixed port/decoder metadata. The
[table models](Airbender/Review/Helpers/Tables/WordROM.lean) enumerate the native
four-MiB profile, including every separator row, every aligned ROM row and UNIMP
padding. Both native fixed queries remain unconditional. Membership derives
address alignment, RAM classification and exact public ROM values; equations
derive port selection, actual masked loads and RAM-only stores. The x0 flag
remains visible until public decoding identifies it. Native Mersenne31 address
addition now derives its carries and ranged output under explicit source/immediate
bounds. Native PC bounds/alignment and clock inputs yield modular successors,
four-tick advancement and port order. The initialized word-memory instance now
recovers every per-row/prior clock input from matching and the actual public
seed/PC boundary, reusing the existing shared clock/history proofs. [Public LW/SW decoding](Airbender/Review/Trace/Families/WordMemory/Decoder.lean)
now recovers actual Sail bytes/decoding and native fields from complete padded
membership. Native Boolean store-mask equations reject padding; generic source,
PC/immediate and register-index proofs are reused. Exact zero flags and incoming
alignment are derived, including stores and original loads to x0. The separate
native registry does not extend the arithmetic execution claim.
[Initialized word-memory history](Airbender/Review/Trace/Families/WordMemory/History.lean)
now derives complete Clean online consistency and newest preceding native reads
for all three ports, including readonly ROM-shadow accesses.
[Native value ranges](Airbender/Review/Trace/Families/WordMemory/Values.lean)
reuse the unchanged decreasing-time induction with proved native load/store/mask
rules: stores copy an earlier operand port; loads select canonical ROM data or
bounded RAM reads. Full decoder membership supplies the zero flag. Actual public
seed reads replace all initial values/clocks, deriving every read, actual write
and terminal word bound without per-row answers. This logical result retains
shadow tokens; it does not identify them with architectural ROM contents.
[Initialized native-row assembly](Airbender/Review/Trace/Families/WordMemory/Inputs.lean)
now obtains source bounds from the first actual port, immediate/PC bounds and
alignment from successful public setup, and all clock inputs from matching.
Existing native address/PC/clock proofs are called unchanged, deriving address
addition, bounded aligned PCs, modular PC successors and native access order.
No per-row numerical interface or desired address/PC result is supplied.
[Actual Sail cell histories](Airbender/Review/Trace/Families/WordMemory/SailHistory.lean)
now reuse shared Clean realization and clock-derived row grouping. The native
mixed-port proof preserves x0: readonly ports copy reads, stores address RAM,
and decoded loads to x0 mask the actual write to zero. Original Sail source GPR
reads and the final mixed register/RAM write are recovered in each instruction
pre-state; readonly aliases stutter. Public RAM alignment remains visible.
Reversed dependent store/load rows derive their intermediate state and later
read, with no supplied intermediate/read/result. The full supplied native cell
image still includes shadow cells tracked as RAM; these cell-transfer results
do not establish architectural ROM-shadow projection or original instruction
execution. Physical boot/padding binding and Sail instruction/platform transport
remain open. The [native shadow theorem](Airbender/Review/Circuits/WordMemory/Theorems.lean)
now derives exact raw read/write value-code equality for every imported RAM port
mapped below four MiB. Full native constraints and metadata suffice: the final
port targets registers or RAM outside that prefix; the earlier ports are
readonly refreshes. The native clock tokens still participate in matching.
The separate [architectural projection](Airbender/Review/Trace/Families/WordMemory/Projection.lean)
now erases whole shadow-address domains from Sail transfers while preserving the
complete native Clean history. [Projection calculations](Airbender/Proofs/Trace/Projection.lean)
prove consistency and latest-write preservation without changing Clean semantics.
[The public initializer](Airbender/Review/Helpers/Memory/ShadowImage.lean) reads
only architectural cells, then appends canonical native shadow seeds supplied as
public initialization data. Domain separation/uniqueness and zero seed clocks
are derived; the shared x0 induction now takes its root from architectural seeds
alone. Native matching, decoder membership and derived clocks supply row order,
actual Sail reads/writes and final architectural matching. Neither desired reads,
intermediate states nor shadow/ROM-value equality are inputs. Ordinary/x0 ROM-load
regressions retain the native shadow refresh even when its location has no Sail
bytes and its value differs from the loaded ROM word. These logical public shadow
seeds are not a proof of the physical native zero-boot profile. Numerical/port
interfaces still need assembly for this projected boundary; physical boot/padding,
ROM-table binding and original instruction execution remain separate.
[Public ROM extraction](Airbender/Review/Helpers/Tables/WordROMImage.lean)
now obtains words by actual original Sail reads. The
[ROM read bridge](Airbender/Review/Trace/Families/WordMemory/ROMImage.lean) recovers
native table data inside the extracted prefix, deriving both data limbs and the
actual effective address. A complete four-MiB extraction discharges prefix
coverage for every native ROM address. Full native UNIMP rows remain present;
missing Sail padding bytes are not filled by extraction. Supplying the actual
Sail boot/padding/shadow state and physical Rust setup/export remain separate.
No expected-read or table-equivalence premise is introduced. The initialized
trace registry remains arithmetic-only.

## Public state, profiles and external inputs

The theorem covers original Sail ADD/ADDI/SUB/LUI/AUIPC execution on the successful
four-byte path, including upstream nextPC initialization and PC retirement.
Public instruction/operand interfaces, actual Sail reads and initial alignment
remain explicit. Selector bits, result bounds, arithmetic and PC effects follow
from the imported constraints. In particular, v2's high-PC wrap is preserved.
The logical history theorem additionally proves newest preceding reads of
injectively encoded native tokens, including readonly timestamp refreshes. Its
initial image may now be constructed from actual public Sail registers/RAM;
missing data fails, and successful reads preserve that state. The supplied public
domain is independent of the witness. This logical image does not yet establish
the physical zero-boot profile or native ROM-shadow interpretation. The [value-bound theorem](Airbender/Review/Trace/Values.lean) now derives native
read/write/terminal bounds. It combines original public seed reads, actual matching,
strict native port order and a zero flag proved from decoder membership. Raw-result
ranges alone do not suffice for a masked write: a concrete bad flag passes local
equations and produces an unbounded write, while full lookup membership rejects it.
The short [Sail-history theorem](Airbender/Review/Trace/SailHistory.lean) now
constructs actual Sail cell transfers and intermediate states. Clean consistency
derives reads from the public seed state; native masked-write equations and the
decoded zero flag preserve hardwired x0, without v3 NOP preprocessing. Alignment
of public RAM cells supplies disjoint byte windows. Native clocks derive complete
row grouping and the PC/state path; readonly refreshes preserve each instruction
pre-state even with aliases. Decoder register indices select original Sail GPR
accessors. These cell transfers do not yet establish instruction execution or
retirement by themselves. The [row assembly](Airbender/Proofs/Trace/Arithmetic.lean)
now derives the complete five-opcode local interfaces and applies original Sail
preparation, execution and retirement. Actual control-register commutation
transports cell histories and supplies rebased PC reads. The resulting state is
the actual masked native write followed by original Sail control updates,
including retained SUB-to-x0. Complete arithmetic trace composition is checked
below. The
[native PC theorem](Airbender/Review/Trace/PC.lean) now derives all incoming PC
bounds/alignment from public indexed setup PCs through RV32 truncation. Native
v2 carry/wrap equations derive bounded outgoing successors. State matching and
the actual public initial PC bound the external terminal PC, including empty
traces. This PC-path result does not establish Sail retirement or whole execution.
[Complete arithmetic execution](Airbender/Review/Trace/Families/AddSub/Theorems.lean)
now composes every native row, in derived clock order, into the original Sail
normal-path relation. The [reference relation](Airbender/Review/Trace/Execution.lean)
checks actual sequential Sail code-byte reads, original decoding, matching PC and
normal preparation/execution/retirement. Native register-space metadata and actual
history prove that all code bytes survive, including bytes outside the tracked
cell domain. Successful selected setup construction retains the actual pure
decoder term, allowing replay in each derived state without a new decoding
premise. State/memory matching derive exact terminal PC/cells, including empty
traces. No row order, intermediate state/read, desired terminal value or table
equivalence is assumed. The reversed dependent ADD/ADDI regression reaches PC 8
and x2=247. Architectural fetch permissions, exceptions, interrupts, other ISA
families, completeness and cryptographic soundness remain outside this checkpoint. The copied custom-operation specification
has no checked v2 consumer yet.

## Verification resources

The [bounded runner](scripts/check_all.py) compiles project modules in dependency
order and caches source/dependency fingerprints. Each proof process and each gate
runs under the shared [macOS watchdog](scripts/bounded_fv.py) with one Lean worker,
Lean -j1/-M3072, physical-footprint ceiling 3072 MiB, resident ceiling 4096 MiB and
finite wall limits. The watchdog is copied from the validated v3 incident response;
it is sampled, not an OS hard ceiling. Small parent/child timeout and allocation
probes verify termination. No native circuit, field or dependency pin changed.
