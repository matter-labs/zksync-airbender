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
masked destination writes, discarded x0 writes and aligned 32-bit PC wraparound.
Decoding, input bounds, preprocessing and actual Sail reads remain explicit local
interfaces. Initialized whole traces, setup extraction and cryptographic argument
soundness are pending. This checkpoint does not inherit v3's completed coverage.

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
lake build Airbender airbender_import airbender_tests Tests.AddSub Tests.PC Tests.CircuitRows Tests.Timestamps Airbender.Checks.Axioms
lake exe airbender_tests
lake exe airbender_import ../../cs/add_sub_lui_auipc_mop_preprocessed_layout.json
python3 scripts/check_axioms.py
python3 scripts/check_review.py
```

Importer rejection tests are not a proof of faithful parsing. The
[trust boundaries](TRUST_AND_REVIEW.md) identify what remains external; the
[plan](FORMAL_VERIFICATION_PLAN.md) gives the next backport milestones.

With Lean's editor extension, inspect the embedded constraints with:

```lean
import Airbender.Review.Circuits.AddSub.Artifact
#print Airbender.AddSub.importedConstraints
```
