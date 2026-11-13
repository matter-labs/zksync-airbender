#!/usr/bin/env python3
"""Test rejection of missing claim proofs, witnesses and unsupported exceptions."""
import copy
import unittest
from check_claim_coverage import validate


class ClaimCoverageTests(unittest.TestCase):
    def setUp(self):
        self.primary = "Example.SoundnessClaim"
        self.witness = "Example.SoundnessSatisfiableClaim"
        self.data = {"claims": {
            self.primary: {"module": "Human.Circuits.Example.Theorems", "head": "forall", "combined": False},
            self.witness: {"module": "Human.Circuits.Example.Theorems", "head": "exists", "combined": False},
        }, "proofs": {self.primary: ["Example.soundness"], self.witness: ["Example.soundness_satisfiable"]}}
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


if __name__ == "__main__":
    unittest.main()
