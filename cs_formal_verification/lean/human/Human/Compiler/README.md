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

[CPU certificate witnesses](../../../proven/Proven/Final/Compiler/CPUCertificates.lean)
give one active certificate for each of the seven CPU families. Each certificate
has full native arithmetic, the supplied logical assignment, all public native
lookups and execute equal to one.

[NativePublicSetup.lean](NativePublicSetup.lean) defines fixed rows, public ROM rows
and PC-indexed decoder rows. Capacity, selector bounds and omitted zero fields are
public setup properties. The
[fixed-row test library](../../../test/Tests/NativeFixedRows/Bindings.lean) compares
complete fixed and fixture-ROM regions with native data. These compiled comparisons
are trusted. The [import guide](../Import/README.md) states the DECISION B binding.

Source snapshots and their JSON conversion are in `proven/`. Certificate procedures
read a source snapshot and the production cached layout through the proved parser.
The kernel checks every term they emit against the imported circuit.
The [drift check](../../../scripts/check_compiler_captures.py) checks content pins,
source sidecars, importer paths and every cached/no-cache description except layers.
CI checks fresh source exports against the pinned snapshots.

[LookupSelectors.lean](LookupSelectors.lean) states complete native query coverage.
[NativeLookups.lean](NativeLookups.lean) defines expanded tuples, and
[LookupArgument.lean](LookupArgument.lean) defines exact natural matching with public
setup rows. A sampled field equation does not establish this matching.
[WorkerLookups.lean](WorkerLookups.lean) covers bigint, BLAKE2 G, BLAKE2 round and the
three split Keccak circuits. [WorkerPublicSetup.lean](WorkerPublicSetup.lean) defines
their public generic, range and timestamp tables.

The proof wrappers use the kernel_exact tactic for large artifact conversions.
The kernel checks the complete theorem type. A regression rejects a term with the
wrong type. The [trust lists](../Trust.lean) state the allowed tactic procedures.
