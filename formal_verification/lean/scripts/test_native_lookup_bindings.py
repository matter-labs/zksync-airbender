"""Reject drift in every generated public lookup-premise instantiation; no Lean job."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class LookupPremiseGeneration(unittest.TestCase):
    def test_all_fourteen_premise_bindings_are_reproduced(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch = Path(directory)
            for relative in ('Airbender/Import/Compiler/LogicalRows',
                             'Airbender/Proofs/GKRProtocol/LogicalRows',
                             'Airbender/Proofs/GKRProtocol/LookupSourceNative',
                             'Airbender/Proofs/GKRProtocol/HelperNative'):
                destination = scratch / relative
                destination.mkdir(parents=True)
                for path in (ROOT / relative).glob('*.lean'):
                    shutil.copyfile(path, destination / path.name)
            audit = scratch / 'Airbender/Checks/Axioms.lean'
            audit.parent.mkdir(parents=True)
            shutil.copyfile(ROOT / 'Airbender/Checks/Axioms.lean', audit)
            command = [sys.executable, '-B', str(ROOT / 'scripts/generate_native_lookup_requests.py'),
                       '--check', '--root', str(scratch)]
            clean = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(clean.returncode, 0, clean.stdout + clean.stderr)
            paths = sorted((scratch / 'Airbender/Import/Compiler/LogicalRows').glob('*.lean'))
            self.assertEqual(len(paths), 14)
            for path in paths:
                text = path.read_text()
                start = text.index('/-- Exact matching of every enabled emitted tuple')
                end = text.index('-- End generated logical lookup argument.', start)
                binding = text[start:end]
                self.assertEqual(binding.count('.native.genericSetupColumns'), 1)
                binding = binding.replace('.native.genericSetupColumns', '.native.range16SetupColumns')
                path.write_text(text[:start] + binding + text[end:])
            changed = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(changed.returncode, 1, changed.stdout + changed.stderr)
            for path in paths:
                self.assertIn(path.relative_to(scratch).as_posix(), changed.stderr)


if __name__ == '__main__':
    unittest.main()
