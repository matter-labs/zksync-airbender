#!/usr/bin/env python3
"""Test rejection of missing claim proofs, witnesses, applications and unsupported exceptions."""
import copy
import unittest
import subprocess
import tempfile
from pathlib import Path
from unittest import mock
import check_claim_coverage
from check_claim_coverage import validate, EXCEPTIONS, AUDIT, ROOT


class ClaimCoverageTests(unittest.TestCase):
    def setUp(self):
        self.primary = "Example.SoundnessClaim"
        self.witness = "Example.SoundnessSatisfiableClaim"
        self.data = {"claims": {
            self.primary: {"module": "Human.Circuits.Example.Theorems", "head": "forall", "combined": False},
            self.witness: {"module": "Human.Circuits.Example.Theorems", "head": "exists", "combined": False},
        }, "proofs": {self.primary: ["Example.soundness"], self.witness: ["Example.soundness_satisfiable"]},
            "telescopes": {f"{self.primary} {self.witness}": None},
            "applications": {f"{self.primary} {self.witness}": None}}
        self.manifest = {"claims": {self.primary: {"witness": self.witness}, self.witness: {}}}

    def test_complete_pair(self):
        self.assertEqual(validate(self.data, self.manifest), 2)

    def test_missing_final_proof(self):
        del self.data["proofs"][self.primary]
        with self.assertRaisesRegex(ValueError, "Missing final proof"):
            validate(self.data, self.manifest)

    def test_missing_witness_statement(self):
        self.manifest["claims"][self.primary]["witness"] = "Example.AbsentSatisfiableClaim"
        with self.assertRaisesRegex(ValueError, "Missing separate non-vacuity statement"):
            validate(self.data, self.manifest)

    def test_witness_must_be_the_stem_witness(self):
        other = "Example.OtherSatisfiableClaim"
        self.data["claims"][other] = copy.copy(self.data["claims"][self.witness])
        self.data["proofs"][other] = ["Example.other_satisfiable"]
        self.manifest["claims"][other] = {}
        self.manifest["claims"][self.primary]["witness"] = other
        self.data["telescopes"] = {f"{self.primary} {other}": None}
        with self.assertRaisesRegex(ValueError, "must be its stem SatisfiableClaim"):
            validate(self.data, self.manifest)

    def test_soundness_stem_witness(self):
        witness = "Example.SatisfiableClaim"
        self.data["claims"][witness] = self.data["claims"].pop(self.witness)
        self.data["proofs"][witness] = self.data["proofs"].pop(self.witness)
        self.manifest["claims"][witness] = self.manifest["claims"].pop(self.witness)
        self.manifest["claims"][self.primary]["witness"] = witness
        self.data["telescopes"] = {f"{self.primary} {witness}": None}
        self.data["applications"] = {f"{self.primary} {witness}": None}
        self.assertEqual(validate(self.data, self.manifest), 2)

    def test_witness_serves_one_claim(self):
        # `Example.SoundnessClaim` and `Example.Claim` have the same stem witness `Example.SatisfiableClaim`.
        shared = "Example.SatisfiableClaim"
        self.data["claims"][shared] = self.data["claims"].pop(self.witness)
        self.data["proofs"][shared] = self.data["proofs"].pop(self.witness)
        self.manifest["claims"][shared] = self.manifest["claims"].pop(self.witness)
        self.manifest["claims"][self.primary]["witness"] = shared
        second = "Example.Claim"
        self.data["claims"][second] = copy.copy(self.data["claims"][self.primary])
        self.data["proofs"][second] = ["Example.claim"]
        self.manifest["claims"][second] = {"witness": shared}
        self.data["telescopes"] = {f"{self.primary} {shared}": None, f"{second} {shared}": None}
        self.data["applications"] = {f"{self.primary} {shared}": None, f"{second} {shared}": None}
        with self.assertRaisesRegex(ValueError, "serves two claims"):
            validate(self.data, self.manifest)

    def test_non_definition_claim(self):
        self.data["non_definitions"] = ["Example.TheoremClaim"]
        with self.assertRaisesRegex(ValueError, "not a Prop-typed definition or structure"):
            validate(self.data, self.manifest)

    def test_missing_witness_proof(self):
        del self.data["proofs"][self.witness]
        with self.assertRaisesRegex(ValueError, "Missing non-vacuity proof"):
            validate(self.data, self.manifest)

    def test_new_claim_requires_inventory(self):
        self.data["claims"]["Example.NewClaim"] = copy.copy(self.data["claims"][self.primary])
        with self.assertRaisesRegex(ValueError, "Claim inventory mismatch"):
            validate(self.data, self.manifest)

    def test_soundness_cannot_use_artifact_exception(self):
        self.manifest["claims"][self.primary] = {"exception": "artifact", "reason": "Not allowed for soundness."}
        with self.assertRaisesRegex(ValueError, "Invalid non-vacuity exception"):
            validate(self.data, self.manifest)

    def test_combined_soundness_and_witness_rejected(self):
        self.data["claims"][self.primary]["combined"] = True
        with self.assertRaisesRegex(ValueError, "are joined"):
            validate(self.data, self.manifest)

    def test_witness_exposes_existential(self):
        self.data["claims"][self.witness]["head"] = "forall"
        with self.assertRaisesRegex(ValueError, "must expose its existential"):
            validate(self.data, self.manifest)

    def test_stale_inventory_row(self):
        self.manifest["claims"]["Example.RemovedClaim"] = {}
        with self.assertRaisesRegex(ValueError, "Claim inventory mismatch"):
            validate(self.data, self.manifest)

    def test_non_proposition_claim(self):
        self.data["non_props"] = ["Example.NumberClaim"]
        with self.assertRaisesRegex(ValueError, "not a proposition"):
            validate(self.data, self.manifest)

    def test_witness_must_match_the_premise_telescope(self):
        self.data["telescopes"][f"{self.primary} {self.witness}"] = "premise 1 differs from the conjunct at its position"
        with self.assertRaisesRegex(ValueError, "is not the premise telescope"):
            validate(self.data, self.manifest)

    def test_listed_telescope_exception(self):
        listed = "Airbender.PlacementsClaim"
        witness = "Airbender.PlacementsSatisfiableClaim"
        for name in (listed, witness):
            self.data["claims"][name] = copy.copy(self.data["claims"][self.witness if name == witness else self.primary])
            self.data["proofs"][name] = ["Example.proof"]
        self.manifest["claims"][listed] = {"witness": witness}
        self.manifest["claims"][witness] = {}
        self.data["telescopes"][f"{listed} {witness}"] = "no premises"
        # A listed claim has no premises, so it has no application to its witness.
        self.assertEqual(validate(self.data, self.manifest), 4)
        self.data["telescopes"][f"{listed} {witness}"] = None
        with self.assertRaisesRegex(ValueError, "Stale premise telescope exception"):
            validate(self.data, self.manifest)
        # A listed claim with premises that its witness omits fails.
        self.data["telescopes"][f"{listed} {witness}"] = "the witness omits premise 2"
        with self.assertRaisesRegex(ValueError, "exception does not hold"):
            validate(self.data, self.manifest)
        # A listed claim with another reason fails, although Lean finds no premises.
        self.data["telescopes"][f"{listed} {witness}"] = "no premises"
        with mock.patch.dict(check_claim_coverage.TELESCOPE_EXCEPTIONS, {listed: "Another reason."}), \
                self.assertRaisesRegex(ValueError, "exception does not hold"):
            validate(self.data, self.manifest)

    def test_missing_application_check(self):
        self.data["applications"] = {}
        with self.assertRaisesRegex(ValueError, "Missing application check"):
            validate(self.data, self.manifest)

    def test_claim_must_apply_to_its_witness(self):
        self.data["applications"][f"{self.primary} {self.witness}"] = "no node of the statement is the claim conclusion"
        with self.assertRaisesRegex(ValueError, "No theorem applies"):
            validate(self.data, self.manifest)

    def test_missing_telescope_check(self):
        self.data["telescopes"] = {}
        with self.assertRaisesRegex(ValueError, "Missing premise telescope check"):
            validate(self.data, self.manifest)

    def test_each_exact_exception_kind(self):
        for kind, names in EXCEPTIONS.items():
            with self.subTest(kind=kind):
                name = sorted(names)[0]
                data = {"claims": {name: self.data["claims"][self.primary]},
                        "proofs": {name: ["Example.fixed_data"]}}
                manifest = {"claims": {name: {"exception": kind, "reason": "Fixed imported data."}}}
                self.assertEqual(validate(data, manifest), 1)
                wrong = name + "Other"
                data["claims"][wrong] = data["claims"].pop(name)
                data["proofs"][wrong] = data["proofs"].pop(name)
                manifest["claims"][wrong] = manifest["claims"].pop(name)
                with self.assertRaisesRegex(ValueError, "Invalid non-vacuity exception"):
                    validate(data, manifest)

    def test_import_module_is_not_an_exception(self):
        self.data["claims"][self.primary]["module"] = "Human.Import.Example"
        self.manifest["claims"][self.primary] = {"exception": "import", "reason": "Module prefix."}
        with self.assertRaisesRegex(ValueError, "Invalid non-vacuity exception"):
            validate(self.data, self.manifest)

    def test_constant_template_is_not_an_exception(self):
        self.data["claims"][self.primary].update(module="Human.ISA.Example", head="constant")
        self.manifest["claims"][self.primary] = {"exception": "constant", "reason": "Template application."}
        with self.assertRaisesRegex(ValueError, "Invalid non-vacuity exception"):
            validate(self.data, self.manifest)

    def test_missing_status_row(self):
        self.data["status_claims"] = [self.primary]
        with self.assertRaisesRegex(ValueError, "Missing claim status rows"):
            validate(self.data, self.manifest)

    def test_complete_status_rows(self):
        self.data["status_claims"] = [self.primary, self.witness]
        self.assertEqual(validate(self.data, self.manifest), 2)

    def test_kernel_telescope_audit(self):
        source = r"""import Lean
set_option linter.unusedVariables false
namespace Smoke
def P (a : Nat) : Prop := a < 5
def R (a : Nat) : Prop := 0 < a
def Claim : Prop := ∀ a : Nat, P a → R a → a < 6
def Exact : Prop := ∃ a : Nat, P a ∧ R a
def Extra : Prop := ∃ a : Nat, P a ∧ R a ∧ a ≠ 0
def Omitted : Prop := ∃ a : Nat, P a
def Weaker : Prop := ∃ a : Nat, a < 10 ∧ R a
def PremisesSwapped : Prop := ∃ a : Nat, R a ∧ P a
def ExtraBinder : Prop := ∃ (a c : Nat), P a ∧ R a
def Fixed : Prop := ∀ {n : Nat} (index : Fin n), index.val < n → index.val < n + 1
def FixedWitness : Prop := ∃ index : Fin 3, index.val < 3
def Pair : Prop := ∀ (a : Nat) (b : Bool), (a = 1 ∧ b = true) → a ≤ 1
def PairExact : Prop := ∃ (a : Nat) (b : Bool), a = 1 ∧ b = true
def BindersSwapped : Prop := ∃ (b : Bool) (a : Nat), a = 1 ∧ b = true
def Order : Prop := ∀ a b : Nat, a + 1 = b → a < b
def ArgumentsSwapped : Prop := ∃ a b : Nat, b + 1 = a
def ProductClaim : Prop := ∀ pair : Nat × Nat, pair.1 < pair.2 → pair.1 ≠ pair.2
def ProductPermuted : Prop := ∃ pair : Nat × Nat, (pair.2, pair.1).1 < (pair.2, pair.1).2
def ProductExact : Prop := ∃ pair : Nat × Nat, pair.1 < pair.2
structure StructuredClaim : Prop where
  sound : ∀ a : Nat, P a → R a → a < 6
structure TwoFieldClaim : Prop where
  first : ∀ a : Nat, P a → a < 5
  second : True
theorem TheoremClaim : True := trivial
def Bounded : Prop := ∀ rows : List Nat, rows ≠ [] → ∀ row ∈ rows, row < 10 → row < 11
def BoundedNested : Prop := ∃ rows : List Nat, rows ≠ [] ∧ ∃ row ∈ rows, row < 10
def ExtraNested : Prop := ∃ a : Nat, P a ∧ R a ∧ ∃ c : Nat, c ≠ a
def ExtraFirst : Prop := ∃ a : Nat, a ≠ 0 ∧ P a ∧ R a
end Smoke
""" + AUDIT + r"""
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.Exact
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.Extra
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.Omitted
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.Weaker
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.PremisesSwapped
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.ExtraBinder
run_cmd ClaimCoverageAudit.audit ``Smoke.Fixed ``Smoke.FixedWitness
run_cmd ClaimCoverageAudit.audit ``Smoke.Pair ``Smoke.PairExact
run_cmd ClaimCoverageAudit.audit ``Smoke.Pair ``Smoke.BindersSwapped
run_cmd ClaimCoverageAudit.audit ``Smoke.Order ``Smoke.ArgumentsSwapped
run_cmd ClaimCoverageAudit.audit ``Smoke.ProductClaim ``Smoke.ProductPermuted
run_cmd ClaimCoverageAudit.audit ``Smoke.ProductClaim ``Smoke.ProductExact
run_cmd ClaimCoverageAudit.audit ``Smoke.StructuredClaim ``Smoke.Exact
run_cmd ClaimCoverageAudit.audit ``Smoke.TwoFieldClaim ``Smoke.Extra
open Lean in
run_cmd do
  let env ← getEnv
  for (name, expected) in [(``Smoke.Claim, true), (``Smoke.StructuredClaim, true), (``Smoke.TwoFieldClaim, true),
      (``Smoke.TheoremClaim, false)] do
    let some info := env.find? name | throwError "missing {name}"
    unless ClaimCoverageAudit.isClaimDeclaration env info == expected do throwError "wrong claim kind: {name}"
  logInfo "CLAIM_KINDS_CHECKED"
run_cmd ClaimCoverageAudit.audit ``Smoke.Bounded ``Smoke.BoundedNested
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.ExtraNested
run_cmd ClaimCoverageAudit.audit ``Smoke.Claim ``Smoke.ExtraFirst
"""
        with tempfile.TemporaryDirectory(prefix="airbender-coverage-test-") as directory:
            path = Path(directory) / "Telescopes.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, 0, result.stdout[-5000:])
        self.assertIn("CLAIM_KINDS_CHECKED", result.stdout)
        verdicts, reasons = {}, {}
        for line in result.stdout.splitlines():
            fields = line.split()
            if fields and fields[0] in {"TELESCOPE_MATCH", "TELESCOPE_MISMATCH"}:
                if fields[1] in {"Smoke.StructuredClaim", "Smoke.TwoFieldClaim"}:
                    reasons[fields[1]] = None if fields[0] == "TELESCOPE_MATCH" else " ".join(fields[3:])
                    continue
                verdicts[fields[2]] = fields[0] == "TELESCOPE_MATCH"
        # A one-field structure states its field; a structure with more fields states a conjunction without premises.
        self.assertEqual(reasons, {"Smoke.StructuredClaim": None, "Smoke.TwoFieldClaim": "no premises"})
        self.assertEqual(verdicts, {
            "Smoke.Exact": True, "Smoke.Extra": True, "Smoke.FixedWitness": True, "Smoke.PairExact": True,
            "Smoke.ProductExact": True, "Smoke.BoundedNested": True, "Smoke.ExtraNested": True,
            "Smoke.ExtraFirst": False,
            "Smoke.Omitted": False, "Smoke.Weaker": False, "Smoke.PremisesSwapped": False,
            "Smoke.ExtraBinder": False, "Smoke.BindersSwapped": False, "Smoke.ArgumentsSwapped": False,
            "Smoke.ProductPermuted": False})

    def test_kernel_application_audit(self):
        source = r"""import Lean
set_option linter.unusedVariables false
namespace Smoke
def P (a : Nat) : Prop := a < 5
def R (a : Nat) : Prop := 0 < a
def Applied : Prop := ∀ a : Nat, P a → R a → a < 6
def AppliedSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
theorem Applied.applied (claim : Applied) : AppliedSatisfiable → ∃ a : Nat, R a ∧ a < 6 :=
  fun ⟨a, p, r⟩ => ⟨a, r, claim a p r⟩
def Weakened : Prop := ∀ a : Nat, P a → R a → a < 6
def WeakenedSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
theorem Weakened.applied (claim : Weakened) : WeakenedSatisfiable → ∃ a : Nat, True :=
  fun ⟨a, p, r⟩ => ⟨a, (fun _ => trivial) (claim a p r)⟩
def Unused : Prop := ∀ a : Nat, P a → R a → a < 6
def UnusedSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
theorem Unused.applied (claim : Unused) : UnusedSatisfiable → ∃ a : Nat, a < 6 :=
  fun ⟨a, p, _⟩ => ⟨a, by unfold P at p; omega⟩
def Closed : Prop := ∀ a : Nat, P a → R a → a < 6
def ClosedSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
theorem Closed.applied (claim : Closed) : ClosedSatisfiable → 0 < 6 :=
  fun ⟨a, p, r⟩ => Nat.lt_of_le_of_lt (Nat.zero_le a) (claim a p r)
def Shared : Prop := ∀ a b : Nat, a = b → a ≤ b
def SharedSatisfiable : Prop := ∃ a b : Nat, a = b
theorem Shared.applied (claim : Shared) : SharedSatisfiable → ∃ a : Nat, a ≤ a :=
  fun ⟨a, b, equal⟩ => ⟨b, by subst equal; exact claim _ _ rfl⟩
def Twice : Prop := ∀ a : Nat, P a → R a → a < 6
def TwiceSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
theorem Twice.first (claim : Twice) : TwiceSatisfiable → ∃ a : Nat, a < 6 := fun ⟨a, p, r⟩ => ⟨a, claim a p r⟩
theorem Twice.second (claim : Twice) : TwiceSatisfiable → ∃ a : Nat, a < 6 := fun ⟨a, p, r⟩ => ⟨a, claim a p r⟩
def Missing : Prop := ∀ a : Nat, P a → R a → a < 6
def MissingSatisfiable : Prop := ∃ a : Nat, P a ∧ R a
def Fixed : Prop := ∀ {n : Nat} (index : Fin n), index.val < n → index.val < n + 1
def FixedSatisfiable : Prop := ∃ index : Fin 3, index.val < 3
theorem Fixed.applied (claim : Fixed) : FixedSatisfiable → ∃ index : Fin 3, index.val < 3 + 1 :=
  fun ⟨index, bound⟩ => ⟨index, claim index bound⟩
def Bounded : Prop := ∀ rows : List Nat, rows ≠ [] → ∀ row ∈ rows, row < 10 → row < 11
def BoundedSatisfiable : Prop := ∃ rows : List Nat, rows ≠ [] ∧ ∃ row ∈ rows, row < 10
theorem Bounded.applied (claim : Bounded) : BoundedSatisfiable → ∃ rows : List Nat, ∃ row ∈ rows, row < 11 :=
  fun ⟨rows, nonempty, row, member, bound⟩ => ⟨rows, row, member, claim rows nonempty row member bound⟩
structure TwoFieldClaim : Prop where
  first : ∀ a : Nat, P a → a < 5
  second : True
end Smoke
""" + AUDIT + r"""
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Applied ``Smoke.AppliedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Weakened ``Smoke.WeakenedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Unused ``Smoke.UnusedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Closed ``Smoke.ClosedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Shared ``Smoke.SharedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Twice ``Smoke.TwiceSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Missing ``Smoke.MissingSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Fixed ``Smoke.FixedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.Bounded ``Smoke.BoundedSatisfiable
run_cmd ClaimCoverageAudit.auditApplication `Smoke ``Smoke.TwoFieldClaim ``Smoke.AppliedSatisfiable
"""
        with tempfile.TemporaryDirectory(prefix="airbender-coverage-test-") as directory:
            path = Path(directory) / "Applications.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, 0, result.stdout[-5000:])
        reasons = {}
        for line in result.stdout.splitlines():
            fields = line.split()
            if fields and fields[0] in {"APPLICATION_MATCH", "APPLICATION_MISMATCH"}:
                reasons[fields[1]] = None if fields[0] == "APPLICATION_MATCH" else " ".join(fields[3:])
        self.assertEqual(reasons, {
            "Smoke.Applied": None, "Smoke.Fixed": None, "Smoke.Bounded": None,
            "Smoke.Weakened": "no node of the statement is the claim conclusion",
            "Smoke.Unused": "the proof does not use both its claim and its witness",
            "Smoke.Closed": "claim binder 1 is not a statement binder",
            "Smoke.Shared": "claim binder 2 shares its statement binder with another claim binder",
            "Smoke.Twice": "2 theorems state the claim applied to its witness, not one",
            "Smoke.Missing": "0 theorems state the claim applied to its witness, not one",
            "Smoke.TwoFieldClaim": "no premises"})

if __name__ == "__main__":
    unittest.main()
