"""Exercise snapshot scheduling and scoped retention without builds or GitHub writes."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest
from unittest.mock import Mock, patch
from urllib.error import HTTPError
from urllib.parse import parse_qs, urlparse

import lean_cache


REPO = Path(__file__).resolve().parents[3]
WORKFLOW = REPO / '.github/workflows/formal-verification.yml'
BASE = 'fv-lean-v3-Linux-X64-' + 'a' * 64 + '-' + 'b' * 64
COMPLETE = BASE + '-complete'
PROGRESS = BASE + '-123-1-progress'
REF = 'refs/heads/codex/fixture'


def cache(cache_id, key, ref=REF, created='2026-11-08T01:00:00Z', size=100):
    return {'id': cache_id, 'key': key, 'ref': ref, 'created_at': created,
            'size_in_bytes': size}


def api_fixture(rows, confirmation=None):
    """Use the real listing/pagination/deletion client with an isolated API."""
    api = lean_cache.GitHub('owner/repo', 'fixture-token')
    lists = 0
    def request(method, path):
        nonlocal lists
        if method == 'DELETE':
            return None
        query = parse_qs(urlparse(path).query)
        if query['page'] == ['1']:
            lists += 1
        selected = confirmation if lists > 1 and confirmation is not None else rows
        start = (int(query['page'][0]) - 1) * 100
        return {'actions_caches': selected[start:start + 100]}
    api.request = Mock(side_effect=request)
    return api


class SnapshotPlan(unittest.TestCase):
    def test_completed_build_uses_content_and_exact_hit_avoids_another_upload(self):
        for progress in (PROGRESS, BASE + '-999-3-progress'):
            self.assertEqual(lean_cache.snapshot_key(COMPLETE, progress, 'success',
                                                    'success', 'false'), COMPLETE)
        for source in ('success', 'failure', 'cancelled'):
            self.assertEqual(lean_cache.snapshot_key(COMPLETE, PROGRESS, source,
                                                    'success', 'true'), '')

    def test_failed_or_bootstrap_only_attempts_keep_run_specific_progress(self):
        for source, bootstrap in (('failure', 'success'), ('cancelled', 'success'),
                                  ('skipped', 'failure'), ('skipped', 'success')):
            self.assertEqual(lean_cache.snapshot_key(COMPLETE, PROGRESS, source,
                                                    bootstrap, ''), PROGRESS)
        self.assertEqual(lean_cache.snapshot_key(COMPLETE, PROGRESS, 'skipped',
                                                'skipped', ''), '')

    def test_invalid_or_mismatched_key_cannot_select_a_snapshot(self):
        for complete, progress in ((COMPLETE + '\nkey=other', PROGRESS),
                                   (COMPLETE.replace('-v3-', '-v2-'), PROGRESS),
                                   (COMPLETE, PROGRESS.replace('b' * 64, 'c' * 64))):
            with self.assertRaises(ValueError):
                lean_cache.snapshot_key(complete, progress, 'success', 'success', '')

    def test_actual_workflow_keys_are_stable_and_legacy_migration_is_separate(self):
        workflow = WORKFLOW.read_text()
        key_inputs = workflow.split('        id: cache-keys\n', 1)[1].split(
            '        run: |\n', 1)[0]
        source_inputs = next(line for line in key_inputs.splitlines()
                             if 'FV_LEAN_SOURCE:' in line)
        for ignored in ('!**/.lake/**', '!**/__pycache__/**', '!**/*.pyc'):
            self.assertIn(ignored, source_inputs)
        block = workflow.split('        id: cache-keys\n', 1)[1].split(
            '      - name:', 1)[0].split('        run: |\n', 1)[1]
        script = textwrap.dedent(block)
        for token, value in (('runner.os', 'Linux'), ('runner.arch', 'X64')):
            script = script.replace('${{ ' + token + ' }}', value)
        results = []
        with tempfile.TemporaryDirectory() as directory:
            for run in ('123', '999'):
                output = Path(directory) / run
                command = script.replace('${{ github.run_id }}', run).replace(
                    '${{ github.run_attempt }}', '1')
                env = dict(os.environ, GITHUB_OUTPUT=str(output),
                           FV_LEAN_TOOLS='a' * 64, FV_LEAN_SOURCE='b' * 64,
                           FV_NATIVE_TOOLS='c' * 64, FV_NATIVE_SOURCE='d' * 64,
                           FV_REPLAY_TOOLS='e' * 64)
                subprocess.run(['bash', '-euo', 'pipefail', '-c', command],
                               env=env, check=True, capture_output=True)
                results.append(dict(line.split('=', 1) for line in
                                    output.read_text().splitlines()))
        self.assertEqual(results[0]['lean-complete'], COMPLETE)
        self.assertEqual(results[1]['lean-complete'], COMPLETE)
        self.assertNotEqual(results[0]['lean-progress'], results[1]['lean-progress'])
        self.assertTrue(results[0]['lean-legacy'].startswith('fv-lean-v2-Linux-X64-'))
        self.assertEqual(results[0]['lean-tool-prefix'], 'fv-lean-v3-Linux-X64-' + 'a' * 64 + '-')

    def test_workflow_saves_only_selected_paths_and_keeps_verification_read_only(self):
        workflow = WORKFLOW.read_text()
        def paths_after(marker):
            block = workflow.split(marker, 1)[1].split('      - ', 1)[0]
            return [line.strip() for line in block.split('          path: |\n', 1)[1]
                    .split('          key:', 1)[0].splitlines()]
        expected = ['formal_verification/lean/.lake/' + suffix for suffix in
                    ('build', 'config', 'packages/Clean', 'packages/lean-sail')]
        self.assertEqual(paths_after('        id: lean-cache\n'), expected)
        self.assertEqual(paths_after('        id: lean-cache-save\n'), expected)
        migration = workflow.split('      - name: Migrate legacy Lean progress', 1)[1].split(
            '      - uses:', 1)[0]
        self.assertIn('uses: actions/cache/restore@v4', migration)
        self.assertIn("steps.lean-cache.outputs.cache-matched-key == ''", migration)
        self.assertIn('inputs.cold_build != true', migration)
        self.assertIn('fv mathlib-cache lake exe cache get', workflow)
        verification, maintenance = workflow.split('  lean-cache-retention:\n', 1)
        self.assertNotIn('actions: write', verification)
        self.assertIn('needs: verification', maintenance)
        self.assertIn('actions: write', maintenance)
        self.assertIn('continue-on-error: true', maintenance)
        self.assertIn("needs.verification.outputs.lean-cache-save == 'success'", maintenance)
        self.assertIn('test_lean_cache', verification)


class Retention(unittest.TestCase):
    def test_only_older_same_branch_lean_entries_are_deleted(self):
        keep = cache(7, COMPLETE, created='2026-11-09T01:00:00Z')
        rows = [cache(1, 'fv-lean-v2-legacy-build'), cache(2, BASE + '-100-1-progress'),
                cache(3, 'fv-native-v3-compiler'), cache(4, 'gpu-compiler-cache'),
                cache(5, 'fv-lean-v2-other-branch', 'refs/heads/main'),
                cache(6, BASE + '-999-1-progress', created='2026-11-10T01:00:00Z'),
                keep, cache(8, 'fv-replay-trusted-v3-controls')]
        api = api_fixture(rows)
        report = lean_cache.prune(api, REF, COMPLETE)
        self.assertEqual(report['id'], 7)
        self.assertEqual(report['size_in_bytes'], 100)
        self.assertEqual(report['deleted'], [1, 2])
        self.assertEqual([call.args for call in api.request.call_args_list if
                          call.args[0] == 'DELETE'],
                         [('DELETE', '/actions/caches/1'), ('DELETE', '/actions/caches/2')])
        self.assertEqual(api.request.call_args_list[0].args[0], 'GET')
        self.assertEqual(api.request.call_args_list[1].args[0], 'GET')

    def test_missing_wrong_branch_prefix_or_empty_replacement_never_deletes(self):
        for replacement in ([], [cache(7, COMPLETE + '-suffix')],
                            [cache(7, COMPLETE, 'refs/heads/main')],
                            [cache(7, COMPLETE, size=0)]):
            api = api_fixture([cache(1, 'fv-lean-v2-old')] + replacement)
            self.assertEqual(lean_cache.prune(api, REF, COMPLETE)['status'], 'not-published')
            self.assertFalse(any(c.args[0] == 'DELETE' for c in api.request.call_args_list))

    def test_disappearing_replacement_or_incomplete_listing_cannot_delete(self):
        api = api_fixture([cache(1, 'fv-lean-v2-old'), cache(7, COMPLETE)], confirmation=[])
        self.assertEqual(lean_cache.prune(api, REF, COMPLETE)['status'], 'replacement-disappeared')
        self.assertFalse(any(c.args[0] == 'DELETE' for c in api.request.call_args_list))
        api = api_fixture([cache(i, 'unrelated') for i in range(100)])
        first = api.request.side_effect
        def fail_page(method, path):
            if 'page=2' in path:
                raise OSError('fixture pagination failure')
            return first(method, path)
        api.request.side_effect = fail_page
        with self.assertRaises(OSError):
            lean_cache.prune(api, REF, COMPLETE)
        self.assertFalse(any(c.args[0] == 'DELETE' for c in api.request.call_args_list))

    def test_replacement_is_found_after_pagination_before_any_delete(self):
        rows = [cache(i, 'unrelated') for i in range(100)] + [cache(101, COMPLETE)]
        api = api_fixture(rows)
        self.assertEqual(lean_cache.prune(api, REF, COMPLETE)['id'], 101)
        self.assertEqual(api.request.call_count, 4)
        for call in api.request.call_args_list:
            query = parse_qs(urlparse(call.args[1]).query)
            self.assertEqual(query['ref'], [REF])
            self.assertEqual(query['key'], ['fv-lean-'])

    def test_partial_replacement_is_also_confirmed_and_unscoped_keys_are_refused(self):
        api = api_fixture([cache(1, 'fv-lean-v2-old'),
                           cache(2, PROGRESS, created='2026-11-09T01:00:00Z')])
        self.assertEqual(lean_cache.prune(api, REF, PROGRESS)['deleted'], [1])
        for ref, key in (('refs/pull/1/merge', COMPLETE), ('refs/heads/', COMPLETE),
                         (REF, 'fv-native-v3-anything'), (REF, 'fv-lean-v2-anything')):
            api = api_fixture([])
            with self.assertRaises(ValueError):
                lean_cache.prune(api, ref, key)
            api.request.assert_not_called()

    def test_read_only_or_unavailable_maintenance_does_not_fail_verification(self):
        env = {'GITHUB_REPOSITORY': 'owner/repo', 'GH_TOKEN': 'fixture-token',
               'GITHUB_REF': REF, 'FV_LEAN_KEEP_KEY': COMPLETE}
        error = HTTPError('https://api.github.com/fixture', 403, 'Forbidden', {}, None)
        with patch.dict(os.environ, env), patch('sys.argv', ['lean_cache.py', 'prune']), \
                patch.object(lean_cache, 'urlopen', side_effect=error), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            lean_cache.main()
        self.assertEqual(json.loads(output.getvalue()),
                         {'status': 'maintenance-unavailable', 'error': 'HTTPError'})
        self.assertNotIn('fixture-token', output.getvalue())
        # A read-only token can list the replacement but cannot DELETE. Stop at
        # the first denial and leave the confirmed replacement untouched.
        api = api_fixture([cache(1, 'fv-lean-v2-old'),
                           cache(2, COMPLETE, created='2026-11-09T01:00:00Z')])
        allowed_read = api.request.side_effect
        def deny_delete(method, path):
            if method == 'DELETE':
                raise error
            return allowed_read(method, path)
        api.request.side_effect = deny_delete
        with patch.dict(os.environ, env), patch('sys.argv', ['lean_cache.py', 'prune']), \
                patch.object(lean_cache, 'GitHub', return_value=api), \
                contextlib.redirect_stdout(io.StringIO()) as output:
            lean_cache.main()
        self.assertEqual(json.loads(output.getvalue())['status'], 'maintenance-unavailable')
        self.assertEqual([call.args for call in api.request.call_args_list
                          if call.args[0] == 'DELETE'], [('DELETE', '/actions/caches/1')])

    def test_api_uses_exact_repository_and_delete_id(self):
        api = lean_cache.GitHub('owner/repo', 'fixture-token')
        with patch.object(lean_cache, 'urlopen', return_value=io.BytesIO(b'')) as open_url:
            api.delete(123)
        request = open_url.call_args.args[0]
        self.assertEqual(request.full_url, 'https://api.github.com/repos/owner/repo/actions/caches/123')
        self.assertEqual(request.method, 'DELETE')
        self.assertEqual(open_url.call_args.kwargs['timeout'], 30)


if __name__ == '__main__':
    unittest.main()
