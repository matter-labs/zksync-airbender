# Trust and review boundaries

## Review entry points

Start with [Properties](Airbender/Review/Helpers/Properties.lean), then the short
[ADD/SUB theorems](Airbender/Review/Circuits/AddSub/Theorems.lean) and their
[Model](Airbender/Review/Circuits/AddSub/Model.lean). The local theorem takes
explicit decoded-input interfaces; it is not an initialized whole-run claim.

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
strict access order under explicit initial/prior clock bounds and alignment;
it does not supply initialized matching or actual memory reads.

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
Exceptions, interrupts, completeness, initialized whole traces and cryptographic
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
