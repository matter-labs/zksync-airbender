"""Native diagnostic hints must build normally and recheck every target."""

from pathlib import Path
import tempfile
import unittest

from check_lean import Runner, native_object_repair_hints


class LeanRepair(unittest.TestCase):
    def test_only_requested_native_objects_are_candidates(self):
        targets = ['+Aesop.Check:o', '+Aesop.Check:olean', '+Aesop.ElabM:o', '+Aesop.ElabM:olean']
        log = ('✖ [2/90] Building Aesop.Check:c.o\n'
               'error: target is out-of-date and needs to be rebuilt\n'
               '✖ [4/90] Building Aesop.ElabM:c.o\n'
               '✖ [5/90] Building Not.Requested:c.o\n')
        self.assertEqual(native_object_repair_hints(targets, log), targets[::2])
        self.assertEqual(native_object_repair_hints(['+Aesop.Check:imports'], log), [])
        self.assertEqual(native_object_repair_hints(targets, 'unexpected Lake diagnostics'), [])

    def exercise(self, hints):
        targets = ['+A:o', '+A:olean', '+B:o', '+B:olean']
        pending = {'+A:o', '+B:o'}
        builds, queries = [], []
        with tempfile.TemporaryDirectory() as directory:
            runner = Runner.__new__(Runner)
            runner.directory = Path(directory)
            runner.repair_count = 0
            runner.object_repair_hints = {tuple(targets): hints}

            def run(label, command, **kwargs):
                self.assertEqual(command[:3], ['lake', '--no-cache', 'build'])
                builds.append(command[-1])
                pending.discard(command[-1])

            def query_pool(label, chunks):
                queries.append(chunks)
                return {}, [chunk for chunk in chunks if pending.intersection(chunk)]

            runner.run, runner.query_pool = run, query_pool
            runner.repair_chunks([targets])
        self.assertFalse(pending)
        self.assertEqual(builds, ['+A:o', '+B:o'])
        self.assertEqual(queries[0], [targets])
        return queries

    def test_complete_hints_replace_bisection_with_normal_builds_and_one_full_requery(self):
        self.assertEqual(len(self.exercise(['+A:o', '+B:o'])), 1)

    def test_incomplete_hints_fall_back_to_original_bisection(self):
        self.assertGreater(len(self.exercise(['+A:o'])), 1)


if __name__ == '__main__':
    unittest.main()
