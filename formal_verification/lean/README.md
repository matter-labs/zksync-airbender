# Circuit verification

## What is checked

[Verification status](VERIFICATION_STATUS.md) lists v2 coverage and open tasks.
The [findings audit](FINDINGS.md) keeps observed behavior separate from unported
v3 findings and missing proof connections.

The proof path is:

```text
v2 compiled layout JSON → native Clean constraints → original Sail execution
```

This is the v2 backport based on dev revision
67ee094449abaebc77e58435f130ce6ea27721e5. Reused definitions and proofs come from
formalization revision 805909325; exact source identities and hashes are in
[provenance](artifacts/provenance.json). Circuit and runtime Rust are unchanged.

Current scope is conditional ADD/ADDI/SUB/LUI/AUIPC row soundness, including actual
masked destination writes, original-opcode discarded x0 writes and aligned
32-bit PC wraparound. Native ten-column decoder placement/query order is checked;
public selected-profile setup construction and logical padded membership are now
connected separately from Rust generation/export fidelity.
Decoding, input bounds, preprocessing and actual Sail reads remain explicit local
interfaces. Native direct port/state metadata now supports
[initialized logical memory history](Airbender/Review/Trace/History.lean): accepted
state/memory matching and initial clock boundaries derive all row/prior clock
bounds, complete Clean memory consistency and latest reads. [Public Sail image construction](Airbender/Review/Trace/Initialization.lean) now
binds seed tokens and initial PC to actual upstream reads, deriving seed bounds,
clocks and uniqueness. [Public decoder recovery](Airbender/Review/Trace/Decoder.lean)
rejects native minus-one padding from the imported mask equations. Logical decoder
membership and initialized history now derive native read/write/terminal word
bounds. [Native-to-Sail history](Airbender/Review/Trace/SailHistory.lean) now derives
actual cell reads/writes and intermediate states, with native x0 preservation and
clock-derived row grouping. Readonly refreshes preserve the instruction pre-state,
including aliases. The [native PC path](Airbender/Review/Trace/PC.lean) now derives
all incoming bounds/alignment, bounded RV32 successors and the terminal PC bound.
Complete instruction interfaces, Rust setup generation/export,
whole Sail execution and cryptographic argument soundness remain pending. This checkpoint does not inherit v3's completed coverage.

## Read these first

The [Review guide](Airbender/Review/README.md) has two routes:
[individual circuit review](Airbender/Review/Circuits/README.md) and
[whole-trace review](Airbender/Review/Trace/README.md).

[Properties](Airbender/Review/Helpers/Properties.lean) defines soundness,
completeness and the observable circuit relation. Shared helpers are grouped by
[topic](Airbender/Review/Helpers/README.md). The public ADD/SUB surface is two
theorems in [Theorems](Airbender/Review/Circuits/AddSub/Theorems.lean), with
observables and assumptions in [Model](Airbender/Review/Circuits/AddSub/Model.lean).
Calculations stay in Proofs; Import has its own fidelity boundary.

## Clean and Sail

Dependencies are unchanged: Lean v4.31.0, Clean
1e563b9c27991b3795eb440c1ee0757edb4ce8b1 and the same Mathlib/lean-sail pins.
[Preparation](scripts/prepare_clean.py) guards Clean's original hashes before
applying the existing compatibility fixes. Native Clean expressions, assertions,
static tables and constraint satisfaction remain the only constraint semantics.

The [unchanged upstream Sail sources](vendor/sail-riscv/source/model/extensions/I/base_insts.sail)
and [generated Lean](generated/sail-rv32/SailRV32.lean) retain their original pins.
[Regeneration](generated/sail-rv32/README.md) documents source/compiler provenance.
No local replacement instruction semantics were added. The existing word and
Sail execution lemmas are copied unchanged; the artifact-specific proof is new.
The pinned custom-operation reference is retained for later work; no v2 custom
operation claim is made yet.

## Reproduce

Run from formal_verification/lean:

```sh
python3 scripts/prepare_clean.py
python3 scripts/check_resource_guard.py
python3 scripts/check_all.py
```

[The serial verification runner](scripts/check_all.py) checks each module with
one Lean thread and a 3072 MiB Lean allocation cap. The shared
[macOS watchdog](scripts/bounded_fv.py) limits the owned process tree to 3072 MiB
physical footprint, 4096 MiB resident memory and a finite wall budget, kills owned
processes after a violation and confirms termination. It uses a global lock and
rejects multiple Lean workers. These are sampled process measurements, not an OS
hard physical-memory ceiling. Redesign a proof when it exceeds the limits.
Dependency bootstrap also needs these limits; do not launch unbounded proof builds.

Importer rejection tests are not a proof of faithful parsing. The
[trust boundaries](TRUST_AND_REVIEW.md) identify what remains external; the
[plan](FORMAL_VERIFICATION_PLAN.md) gives the next backport milestones.

With Lean's editor extension, inspect the embedded constraints with:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
