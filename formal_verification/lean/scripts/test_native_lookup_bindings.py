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
                             'Airbender/Proofs/GKRProtocol/DecoderArgumentsNative',
                             'Airbender/Proofs/GKRProtocol/ProgramDecoderNative',
                             'Airbender/Proofs/GKRProtocol/ProgramDecoderLookup',
                             'Airbender/Proofs/GKRProtocol/ProgramFixedLookup',
                             'Airbender/Proofs/GKRProtocol/ProgramConstraintsNative',
                             'Airbender/Proofs/GKRProtocol/ProgramPCLowNative',
                             'Airbender/Proofs/GKRProtocol/PhysicalClosedNative',
                             'Airbender/Proofs/GKRProtocol/HelperNative'):
                destination = scratch / relative
                destination.mkdir(parents=True)
                for path in (ROOT / relative).glob('*.lean'):
                    shutil.copyfile(path, destination / path.name)
            audit = scratch / 'Airbender/Checks/Axioms.lean'
            audit.parent.mkdir(parents=True)
            shutil.copyfile(ROOT / 'Airbender/Checks/Axioms.lean', audit)
            for relative in ('Airbender/Review/Compiler/ProgramLogicalRows.lean',
                             'Airbender/Proofs/GKRProtocol/ProgramLogicalRows.lean',
                             'Airbender/Data/Compiler/NativeProgramSetup.lean',
                             'Airbender/Proofs/GKRProtocol/ProgramSetupNative.lean'):
                destination = scratch / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, destination)
            for name in ('add-sub', 'jump-branch', 'mul-div', 'shift-binop',
                         'word-memory', 'subword-memory', 'unified'):
                relative = Path('artifacts/setup') / (name + '.json')
                destination = scratch / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, destination)
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
                self.assertEqual(binding.count('.native.genericSetupColumns'), 2)
                binding = binding.replace('.native.genericSetupColumns', '.native.range16SetupColumns')
                path.write_text(text[:start] + binding + text[end:])
            changed = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(changed.returncode, 1, changed.stdout + changed.stderr)
            for path in paths:
                self.assertIn(path.relative_to(scratch).as_posix(), changed.stderr)
            restored = subprocess.run([item for item in command if item != '--check'],
                                      capture_output=True, text=True)
            self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
            decoder_paths = sorted((scratch / 'Airbender/Proofs/GKRProtocol/ProgramDecoderNative').glob('*.lean'))
            self.assertEqual(len(decoder_paths), 14)
            for path in decoder_paths:
                text = path.read_text()
                self.assertIn('.fields.map', text)
                path.write_text(text.replace('.fields.map', '.fields.reverse.map', 1))
            changed = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(changed.returncode, 1, changed.stdout + changed.stderr)
            for path in decoder_paths:
                self.assertIn(path.relative_to(scratch).as_posix(), changed.stderr)


if __name__ == '__main__':
    unittest.main()
