# Cached compiler captures

[Capture.lean](Capture.lean) defines a cached circuit and its public profile.
The [ADD/SUB capture](Captures/AddSub.lean) and the other family modules import
14 cached production layouts with the [proved circuit parser](../Import/Transcribe.lean).
Each import reads its pinned file in `cs/compiled_circuits/`.
Large gate, cache and placement arrays retain shared literal declarations.

Each capture states description equality, arithmetic preservation and an arithmetic
witness. Only compiled layers differ from the no-cache description.
[Theorems.lean](Theorems.lean) imports all captures.

[NativeTargets.lean](NativeTargets.lean) gives three machine corollaries.
[NativeMachineArguments.lean](NativeMachineArguments.lean) supplies cached CPU gates,
placement, participation and exact native lookup matching. These derive CPU clock
constraints and public decoder membership.
[WorkerCertificates.lean](WorkerCertificates.lean) supplies cached worker gates,
placement, exact public lookups and participation. The target proofs derive the complete
worker row constraints from them. Certificates describe each submitted worker pool in order.
State, request and shared memory matching are explicit interfaces.
The padded native arguments also accept padding rows with execute zero. The padded native
targets keep every row in the masked state, request and memory relations.

[NativeMemory.lean](NativeMemory.lean) gives the extension semantics of memory tuples, lookup
caches and RAM-product gates. [MemoryPorts.lean](MemoryPorts.lean) states one claim for each
cached CPU circuit: native base gates, extension caches and product gates give the RAM read and
write outputs. Each output is the product of the encoded port tokens and PC-state token of the
model row, masked by the execute column. `StateTokenMatchingClaim` gives the raw state matching
from exact matching of the PC-state tokens.
[WorkerMemoryPorts.lean](WorkerMemoryPorts.lean) states the same claim for the six worker circuits.
Each worker output is the product of the encoded port tokens and request token of the worker
row, masked by the execute column.
[MemoryComposition.lean](MemoryComposition.lean) splits the single native RAM permutation of each
machine by address class into the state, request and memory relations of the native machine arguments.
[CertificateMemory.lean](CertificateMemory.lean) gives the extension values of the native certificates
under shared challenges. With them each certificate gives the RAM outputs of its row.
[PermutationTargets.lean](PermutationTargets.lean) states the native targets with the single RAM
permutation as the only matching premise; the padded targets take the masked permutation.

[CPU certificate witnesses](../../../proven/Proven/Final/Compiler/CPUCertificates.lean)
give one active certificate for each of the seven CPU families. Each certificate
has full native arithmetic, the supplied logical assignment, all public native
lookups and execute equal to one.

[NativePublicSetup.lean](NativePublicSetup.lean) defines fixed rows, public ROM rows
and PC-indexed decoder rows. Capacity, selector bounds and omitted zero fields are
public setup properties. The `…ImportClaim` statements of
[NativeSetups/Claims.lean](NativeSetups/Claims.lean) make the public generic rows of each CPU circuit for the setup
fixture program ([NativeSetups/Fixture.lean](NativeSetups/Fixture.lean): its initial state and its program image) equal
to the imported native setups: the fixed rows of [NativeFixedRows.lean](NativeFixedRows.lean) and the shift/byte
rows, the fixture-ROM rows, the decoder rows with their tag, and the padding rows;
[NativeSetups/Ranges.lean](NativeSetups/Ranges.lean) does the same for the range columns. These claim modules read
the raw setup data, and the definitions do not import them. The [import guide](../Import/README.md) states the setup binding.

Source snapshots and their JSON conversion are in `proven/`. Certificate procedures
read a source snapshot and the production cached layout through the proved parser.
The kernel checks every term they emit against the imported circuit.
The [drift check](../../../scripts/check_compiler_captures.py) checks content pins,
source sidecars, importer paths and every cached/no-cache description except layers.
CI checks fresh source exports against the pinned snapshots.

[LookupSelectors.lean](LookupSelectors.lean) states complete native query coverage.
It also states which setup columns the table side of each lookup group reads.
[NativeLookups.lean](NativeLookups.lean) defines expanded tuples, and
[LookupArgument.lean](LookupArgument.lean) defines exact natural matching with public
setup rows. A sampled field equation does not establish this matching.
[WorkerLookups.lean](WorkerLookups.lean) covers bigint, BLAKE2 G, BLAKE2 round and the
three split Keccak circuits. [WorkerPublicSetup.lean](WorkerPublicSetup.lean) defines
their public generic, range and timestamp tables.

The proof wrappers use the kernel_exact tactic for large artifact conversions.
The kernel checks the complete theorem type. A regression rejects a term with the
wrong type. The [trust lists](../Trust.lean) state the allowed tactic procedures.
