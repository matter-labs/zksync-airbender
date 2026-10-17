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
queries are emitted as native Clean operations. Unsupported nonempty fixed
lookups, byte ranges and state linkage fail closed. Native stage-two arguments,
public boundary conditions, decoder tables and memory matching are not implied
by this projection. Their remaining work is explicit in the status and plan.

Logical variable IDs are recovered uniquely from physical column placement.
The [named mapping](Airbender/Review/Circuits/AddSub/Model.lean) exposes actual
destination-write variables 37/38 rather than raw arithmetic variables 29/30.
The proof connects both using the imported x0 mask equations. Pinning and parser
regressions check parts of this connection; formal parsing/emission fidelity is
not proved.

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
retirement; complete local-interface assembly remains pending. The
[native PC theorem](Airbender/Review/Trace/PC.lean) now derives all incoming PC
bounds/alignment from public indexed setup PCs through RV32 truncation. Native
v2 carry/wrap equations derive bounded outgoing successors. State matching and
the actual public initial PC bound the external terminal PC, including empty
traces. This PC-path result does not establish Sail retirement or whole execution.
Exceptions, interrupts, completeness, whole Sail execution and cryptographic
soundness are outside this checkpoint. The copied custom-operation specification
has no checked v2 consumer yet.

## Verification resources

The [bounded runner](scripts/check_all.py) compiles project modules in dependency
order and caches source/dependency fingerprints. Each proof process and each gate
runs under the shared [macOS watchdog](scripts/bounded_fv.py) with one Lean worker,
Lean -j1/-M3072, physical-footprint ceiling 3072 MiB, resident ceiling 4096 MiB and
finite wall limits. The watchdog is copied from the validated v3 incident response;
it is sampled, not an OS hard ceiling. Small parent/child timeout and allocation
probes verify termination. No native circuit, field or dependency pin changed.
