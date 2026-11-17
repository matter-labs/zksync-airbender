#!/usr/bin/env python3
"""Test rejection of missing claim proofs, witnesses and unsupported exceptions."""
import copy
import unittest
import subprocess
import tempfile
from pathlib import Path
from check_claim_coverage import validate, EXCEPTIONS, EVIDENCE_MODULE, EVIDENCE_AUDIT, ROOT, evidence_source


class ClaimCoverageTests(unittest.TestCase):
    def setUp(self):
        self.primary = "Example.SoundnessClaim"
        self.witness = "Example.SoundnessSatisfiableClaim"
        self.data = {"claims": {
            self.primary: {"module": "Human.Circuits.Example.Theorems", "head": "forall", "combined": False},
            self.witness: {"module": "Human.Circuits.Example.Theorems", "head": "exists", "combined": False},
        }, "proofs": {self.primary: ["Example.soundness"], self.witness: ["Example.soundness_satisfiable"]},
            "applications": [(self.primary, self.witness)]}
        self.manifest = {"claims": {self.primary: {"witness": self.witness, "evidence": EVIDENCE_MODULE}, self.witness: {}}}

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
        self.data["applications"] = [(self.primary, other)]
        with self.assertRaisesRegex(ValueError, "must be its stem SatisfiableClaim"):
            validate(self.data, self.manifest)

    def test_soundness_stem_witness(self):
        witness = "Example.SatisfiableClaim"
        self.data["claims"][witness] = self.data["claims"].pop(self.witness)
        self.data["proofs"][witness] = self.data["proofs"].pop(self.witness)
        self.manifest["claims"][witness] = self.manifest["claims"].pop(self.witness)
        self.manifest["claims"][self.primary]["witness"] = witness
        self.data["applications"] = [(self.primary, witness)]
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
        self.manifest["claims"][second] = {"witness": shared, "evidence": EVIDENCE_MODULE}
        self.data["applications"] = [(self.primary, shared), (second, shared)]
        with self.assertRaisesRegex(ValueError, "serves two claims"):
            validate(self.data, self.manifest)

    def test_non_definition_claim(self):
        self.data["non_definitions"] = ["Example.StructureClaim"]
        with self.assertRaisesRegex(ValueError, "not a Prop-typed definition"):
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

    def test_missing_typed_evidence(self):
        del self.manifest["claims"][self.primary]["evidence"]
        with self.assertRaisesRegex(ValueError, "Missing typed witness evidence"):
            validate(self.data, self.manifest)

    def test_prose_is_not_typed_evidence(self):
        self.manifest["claims"][self.primary]["evidence"] = "The premises can hold."
        with self.assertRaisesRegex(ValueError, "Missing typed witness evidence"):
            validate(self.data, self.manifest)

    def test_different_claim_witness_is_rejected(self):
        self.data["applications"] = [(self.primary, "Example.OtherSatisfiableClaim")]
        with self.assertRaisesRegex(ValueError, "application to its own witness"):
            validate(self.data, self.manifest)

    def test_missing_claim_application(self):
        self.data["applications"] = []
        with self.assertRaisesRegex(ValueError, "application to its own witness"):
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

    def test_evidence_keeps_lean_examples_and_names_only_typed_applications(self):
        source = "import Human.Example\nexample (claim : Example.Claim) : Example.SatisfiableClaim → True := by trivial\n"
        named, names = evidence_source(source)
        self.assertEqual(names, ["Checks.ClaimCoverage.case0"])
        self.assertIn("theorem _root_.Checks.ClaimCoverage.case0 (claim :", named)
        self.assertNotIn("import Human.Example", named)

    def test_missing_status_row(self):
        self.data["status_claims"] = [self.primary]
        with self.assertRaisesRegex(ValueError, "Missing claim status rows"):
            validate(self.data, self.manifest)

    def test_complete_status_rows(self):
        self.data["status_claims"] = [self.primary, self.witness]
        self.assertEqual(validate(self.data, self.manifest), 2)

    def test_kernel_evidence_audit(self):
        source = r'''import Lean
namespace Airbender
inductive Expr where
  | sample
end Airbender
open Airbender
set_option linter.unusedVariables false
namespace Smoke
def Claim : Prop := ∀ n : Nat, n = n
def Witness : Prop := ∃ n : Nat, 0 < n
def ConjunctionClaim : Prop := (∀ n : Nat, n = n) ∧ True
structure Bundle : Prop where
  proof : ∀ n : Nat, n = n
def StructuredClaim : Prop := Bundle ∧ True
theorem valid (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, claim n⟩
theorem projection (claim : ConjunctionClaim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, claim.1 n⟩
theorem structured (claim : StructuredClaim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, claim.1.proof n⟩
theorem noClaim (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, rfl⟩
theorem noWitness (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun _ => ⟨0, claim 0⟩
theorem wrongData (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨0, claim 0⟩
theorem arithmeticData (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n + 1, claim (n + 1)⟩
theorem cancelledData (claim : Claim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n - n, claim (n - n)⟩
def ProductClaim : Prop := ∀ pair : Nat × Nat, pair = pair
theorem constructorData (claim : ProductClaim) : Witness → ∃ pair : Nat × Nat, pair = pair :=
  fun ⟨n, _⟩ => ⟨(n, n), claim (n, n)⟩
theorem secondApplication (claim : Claim) : Witness → ∃ n : Nat, n = n ∧ n + 1 = n + 1 :=
  fun ⟨n, _⟩ => ⟨n, claim n, claim (n + 1)⟩
def PairClaim : Prop := ∀ {m : Nat} (n k : Nat), m = m ∧ n = n ∧ k = k
theorem implicitConstant (claim : PairClaim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, (claim (m := 0) n n).2.1⟩
theorem partialData (claim : PairClaim) : Witness → ∃ n : Nat, n = n :=
  fun ⟨n, _⟩ => ⟨n, (claim (m := n) n 0).2.1⟩
structure StructureClaim : Prop where
  proof : True
theorem TheoremClaim : True := trivial
end Smoke
''' + EVIDENCE_AUDIT + r'''
open Lean in
run_cmd do
  let env ← getEnv
  for (name, definition) in [(``Smoke.Claim, true), (``Smoke.StructureClaim, false), (``Smoke.TheoremClaim, false)] do
    let some info := env.find? name | throwError "missing {name}"
    unless ClaimCoverageAudit.isPropDefinition info == definition do
      throwError "wrong claim kind: {name}"
  logInfo "CLAIM_KINDS_CHECKED"
run_cmd ClaimCoverageAudit.audit ``Smoke.valid
run_cmd ClaimCoverageAudit.audit ``Smoke.projection
run_cmd ClaimCoverageAudit.audit ``Smoke.structured
/-- error: Evidence does not apply its claim: Smoke.noClaim -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.noClaim
/-- error: Evidence does not use its witness: Smoke.noWitness -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.noWitness
/-- error: Evidence does not apply its claim to its witness data: Smoke.wrongData -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.wrongData
/-- error: Evidence does not apply its claim to its witness data: Smoke.arithmeticData -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.arithmeticData
/-- error: Evidence does not apply its claim to its witness data: Smoke.cancelledData -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.cancelledData
/-- error: Evidence does not apply its claim to its witness data: Smoke.secondApplication -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.secondApplication
run_cmd ClaimCoverageAudit.audit ``Smoke.constructorData
run_cmd ClaimCoverageAudit.audit ``Smoke.implicitConstant
/-- error: Evidence does not apply its claim to its witness data: Smoke.partialData -/
#guard_msgs in
run_cmd ClaimCoverageAudit.audit ``Smoke.partialData
'''
        named, names = evidence_source("namespace Smoke\n"
            "example (claim : Claim) : Witness → ∃ n : Nat, n = n :=\n"
            "  fun ⟨n, _⟩ => ⟨n, claim n⟩\nend Smoke\n")
        source += named + f"\nrun_cmd ClaimCoverageAudit.audit ``{names[0]}\n"
        with tempfile.TemporaryDirectory(prefix="airbender-coverage-test-") as directory:
            path = Path(directory) / "Evidence.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertEqual(result.returncode, 0, result.stdout[-5000:])
        self.assertIn("WITNESS_APPLICATION Smoke.Claim Smoke.Witness", result.stdout)
        self.assertIn("WITNESS_APPLICATION Smoke.ConjunctionClaim Smoke.Witness", result.stdout)
        self.assertIn("WITNESS_APPLICATION Smoke.StructuredClaim Smoke.Witness", result.stdout)
        self.assertIn("WITNESS_APPLICATION Smoke.PairClaim Smoke.Witness", result.stdout)
        self.assertIn("WITNESS_APPLICATION Smoke.ProductClaim Smoke.Witness", result.stdout)
        self.assertIn("CLAIM_KINDS_CHECKED", result.stdout)


if __name__ == "__main__":
    unittest.main()
