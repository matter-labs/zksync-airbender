import itertools
from pathlib import Path
import unittest

from run_lean_diagnosis import ASSURANCE_FLAGS, command, requested_modules


class LeanDiagnosis(unittest.TestCase):
    def test_normal_validation_accepts_all_assurance_flag_combinations(self):
        for values in itertools.product(("true", "false"), repeat=len(ASSURANCE_FLAGS)):
            self.assertEqual(requested_modules(dict(zip(ASSURANCE_FLAGS, values))), ())

    def test_diagnosis_rejects_every_nonempty_assurance_flag_combination(self):
        for values in itertools.product(("true", "false"), repeat=len(ASSURANCE_FLAGS)):
            if "true" not in values:
                continue
            with self.subTest(values=values), self.assertRaises(ValueError):
                requested_modules({"FV_DIAGNOSE_MODULES": "Tests.PathGLoopNative",
                                   **dict(zip(ASSURANCE_FLAGS, values))})

    def test_only_existing_project_modules_are_accepted(self):
        for request in ("Tests.PathGLoopNative;id", "$(id)", "Tests..PathGLoopNative",
                        "../Tests/PathGLoopNative", "--module", "Mathlib.Init",
                        "Tests.DoesNotExist", "Tests.PathGLoopNative Tests.PathGLoopNative",
                        " ".join(f"Tests.Module{i}" for i in range(17))):
            with self.subTest(request=request), self.assertRaises(ValueError):
                requested_modules({"FV_DIAGNOSE_MODULES": request})

    def test_modules_are_separate_arguments_to_the_existing_guarded_frontend(self):
        modules = requested_modules({"FV_DIAGNOSE_MODULES":
                                     "Tests.PathGLoopNative\nTests.UnifiedDelegationShared"})
        self.assertEqual(command(modules, Path("/tmp/diagnosis")),
                         ["python3", "scripts/check_lean.py", "--guard", "scripts/bounded_fv.py",
                          "--workers", "1", "--output", "/tmp/diagnosis",
                          "--module", "Tests.PathGLoopNative",
                          "--module", "Tests.UnifiedDelegationShared"])


if __name__ == "__main__":
    unittest.main()
