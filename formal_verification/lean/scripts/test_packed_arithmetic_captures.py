"""Keep both arithmetic pilot captures complete and preserve unrelated files."""
import json
from pathlib import Path
import re
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import gkr_full_arithmetic_certificate as generator


class PackedArithmeticCaptureTests(unittest.TestCase):
    def test_both_modes_use_one_whole_capture(self):
        self.assertEqual(generator.CHECKER_CAPTURES, {"AddSubCached", "AddSubUncached"})
        for case in sorted(generator.CHECKER_CAPTURES):
            path = generator.LEAN / f"Airbender/Proofs/GKRProtocol/FullArithmeticNative/{case}Foundation.lean"
            quoted = re.search(r'\bselectors\s+("(?:[^"\\]|\\.)*")', path.read_text()).group(1)
            result = json.loads(json.loads(quoted))
            modules = generator.modules("add-sub-" + case.removeprefix("AddSub").lower(), case, result)
            self.assertEqual(len(modules), 2)
            root = modules[-1][1]
            self.assertEqual(root.count("certify_full_compiler_arithmetic native"), 1)
            self.assertNotIn(" start ", root)
            self.assertNotIn(" stop ", root)
            self.assertNotIn("maxHeartbeats", root)

    def test_untracked_retired_path_stops_before_mutation(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "Airbender/Proofs/GKRProtocol/FullArithmeticNative/AddSubCachedUniquePart0.lean"
            path.parent.mkdir(parents=True)
            path.write_text("unrelated user data\n")
            with patch.object(generator.subprocess, "run", return_value=SimpleNamespace(returncode=1)):
                with self.assertRaisesRegex(ValueError, "untracked arithmetic module"):
                    generator.retired_checker_parts(root, "AddSubCached", [])
            self.assertEqual(path.read_text(), "unrelated user data\n")

    def test_retirement_stays_within_selected_capture(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            parent = root / "Airbender/Proofs/GKRProtocol/FullArithmeticNative"
            parent.mkdir(parents=True)
            for name in ["AddSubCachedUniquePart0", "AddSubCachedNotesPart0", "UnifiedCachedUniquePart0"]:
                (parent / (name + ".lean")).write_text("preserve\n")
            with patch.object(generator.subprocess, "run", return_value=SimpleNamespace(returncode=0)):
                retired = generator.retired_checker_parts(root, "AddSubCached", [])
            self.assertEqual([path.name for path in retired], ["AddSubCachedUniquePart0.lean"])
            self.assertTrue(all(path.read_text() == "preserve\n" for path in parent.glob("*.lean")))


if __name__ == "__main__":
    unittest.main()
