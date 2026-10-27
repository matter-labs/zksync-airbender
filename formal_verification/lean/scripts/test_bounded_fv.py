#!/usr/bin/env python3
"""Lightweight bounded_fv controls; no compiler, export or large allocation.

Run ParserTests inside the existing guard if desired. Run ProcessTests only as
an UNWRAPPED lightweight orchestrator when the worker is idle: each child uses
the one real global lock/guard sequentially. Nesting it in a guard is invalid.
Linux runtime controls must also pass on the Linux CI host; Darwin execution
cannot establish Linux pidfd/subreaper behavior.
"""

import contextlib
import ctypes
import fcntl
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import Mock, patch

import bounded_fv as guard

SCRIPT = Path(guard.__file__).resolve()


def proc_stat(pid=42, comm='name ) with spaces', birth=987, ppid=1, pgrp=42, session=42):
    fields = ['S', str(ppid), str(pgrp), str(session)] + ['0'] * 15 + [str(birth)] + ['0'] * 30
    return f'{pid} ({comm}) ' + ' '.join(fields)


def rollup(**changes):
    values = dict(Rss=500000, Anonymous=1024, Pss_Shmem=128, Swap=256,
                  Private_Hugetlb=0, Shared_Hugetlb=0)
    values.update(changes)
    return '00000000-ffffffff ---p 00000000 00:00 0 [rollup]\n' + ''.join(
        f'{key}: {value} kB\n' for key, value in values.items())


class ParserTests(unittest.TestCase):
    def test_proc_identity_handles_comm_parentheses_and_newlines(self):
        actual = guard.parse_proc_stat(proc_stat(comm='worker ) test\n( name'))
        self.assertEqual((actual.pid, actual.birth, actual.ppid, actual.pgrp, actual.session),
                         (42, 987, 1, 42, 42))
        self.assertEqual(actual.name, 'worker ) test\n( name')

    def test_proc_identity_rejects_malformed_or_truncated_data(self):
        for value in ('42 broken', '42 (name) S 1', proc_stat(birth=-1)):
            with self.subTest(value=value), self.assertRaises(ValueError):
                guard.parse_proc_stat(value)
        self.assertEqual(guard.parse_proc_stat(proc_stat(birth=0)).birth, 0)
        self.assertEqual(guard.parse_proc_stat(proc_stat(pgrp=-1, session=-1)).pgrp, -1)

    def test_charged_proxy_excludes_readonly_file_cache(self):
        charged, resident, bounded = guard.parse_smaps_rollup(rollup())
        self.assertEqual(charged, (1024 + 128 + 256) * 1024)
        self.assertEqual(resident, 500000 * 1024)
        self.assertEqual(bounded, (1024 + 128) * 1024)
        huge_charge, huge_resident, _ = guard.parse_smaps_rollup(rollup(Private_Hugetlb=64, Shared_Hugetlb=32))
        self.assertEqual((huge_charge - charged, huge_resident - resident), (96 * 1024, 96 * 1024))

    def test_linux_mapped_files_are_telemetry_but_anonymous_memory_is_bounded(self):
        args = guard.parse_args(['--mib', '8', '--resident-mib', '16', '--seconds', '1', '--log', 'unused', '--', 'true'])
        mapped = guard.Sample(guard.ProcessInfo(42, 987, 'lean'), 1, 8192 << 20, 1)
        self.assertIsNone(guard.budget_reason([mapped], args, 0))
        anonymous = guard.Sample(mapped.info, 9 << 20, mapped.resident, 9 << 20)
        self.assertEqual(guard.budget_reason([anonymous], args, 0), 'memory budget exceeded')

    def test_linux_mm_disappears_before_zombie_state(self):
        backend = guard.LinuxBackend()
        info = guard.parse_proc_stat(proc_stat())
        for error in (FileNotFoundError(), ProcessLookupError()):
            with self.subTest(error=error), patch.object(backend, 'info', return_value=info), patch.object(
                    backend, 'pin'), patch.object(Path, 'read_text', side_effect=error):
                sample = backend.measure(42, 987)
                self.assertEqual((sample.info.birth, sample.footprint, sample.resident), (987, 0, 0))
        with patch.object(backend, 'info', return_value=info), patch.object(backend, 'pin'), patch.object(
                Path, 'read_text', side_effect=PermissionError()), self.assertRaises(PermissionError):
            backend.measure(42, 987)

    def test_linux_mm_exit_does_not_hide_pid_reuse(self):
        backend = guard.LinuxBackend()
        before, after = guard.parse_proc_stat(proc_stat()), guard.parse_proc_stat(proc_stat(birth=999))
        with patch.object(backend, 'info', side_effect=[before, after]), patch.object(backend, 'pin'), patch.object(
                Path, 'read_text', side_effect=ProcessLookupError()), self.assertRaises(guard.IdentityChanged):
            backend.measure(42, 987)

    def test_linux_supervisor_keeps_ownership_until_cleanup_succeeds(self):
        backend, child, tracker = Mock(), Mock(), Mock()
        backend.libc.prctl.return_value = 0
        child.returncode = 0
        child.poll.return_value = 0
        with patch.object(guard, 'LinuxBackend', return_value=backend), patch.object(
                guard.subprocess, 'Popen', return_value=child), patch.object(guard, 'Tracker', return_value=tracker), patch.object(
                guard.os, 'getppid', return_value=42), patch.object(guard.signal, 'signal'), patch.object(
                guard.time, 'sleep'), patch.object(guard, 'cleanup', side_effect=[([43], ['deadline']), ([], [])]) as cleanup:
            self.assertEqual(guard.linux_payload_owner(42, ['payload']), 0)
            self.assertEqual(cleanup.call_count, 2)
            backend.close.assert_called_once()

    def test_guard_requests_supervisor_cleanup_without_killing_its_lock_owner(self):
        backend, child, tracker = Mock(), Mock(), Mock()
        backend.adopted_children = True
        child.pid, child.returncode = 42, 0
        tracker.owned, tracker.samples = {42: 987, 43: 988}, {}
        guard.cleanup(child, tracker, backend, preserve_supervisor=True)
        backend.terminate.assert_any_call(42, 987, signal.SIGTERM)
        backend.terminate.assert_any_call(43, 988)

    def test_missing_duplicate_malformed_counters_fail_closed(self):
        bad = [rollup().replace('Swap: 256 kB\n', ''), rollup() + 'Rss: 1 kB\n',
               rollup().replace('Anonymous: 1024 kB', 'Anonymous: -1 kB'),
               rollup().replace('Rss: 500000 kB', 'Rss: 500000 bytes'), rollup(Rss=1)]
        for value in bad:
            with self.subTest(value=value[:80]), self.assertRaises(ValueError):
                guard.parse_smaps_rollup(value)

    def test_caps_require_review_for_extended_time(self):
        base = ['--mib', '2560', '--resident-mib', '5120', '--log', '/tmp/unused-bounded-parser.log']
        self.assertEqual(guard.parse_args(base + ['--seconds', '900', '--', 'true']).seconds, 900)
        self.assertTrue(guard.parse_args(base + ['--seconds', '1800', '--review', '--', 'true']).review)
        for extra in (['--mib', '2561', '--seconds', '1'], ['--seconds', '901'],
                      ['--seconds', '1801', '--review'], ['--seconds', 'nan'],
                      ['--resident-mib', '5121', '--seconds', '1']):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                guard.parse_args(base + extra + ['--', 'true'])

    def test_one_lean_worker_and_independent_memory_caps(self):
        args = guard.parse_args(['--mib', '8', '--resident-mib', '16', '--seconds', '1', '--log', 'unused', '--', 'true'])
        sample = guard.Sample(guard.ProcessInfo(1, 10, 'lean'), 1, 1)
        self.assertEqual(guard.budget_reason([sample, sample], args, 0), 'more than one Lean worker')
        cache = guard.Sample(guard.ProcessInfo(2, 20, 'worker'), 1, 17 << 20)
        self.assertEqual(guard.budget_reason([cache], args, 0), 'memory budget exceeded')
        charged = guard.Sample(guard.ProcessInfo(2, 20, 'worker'), 9 << 20, 1)
        self.assertEqual(guard.budget_reason([charged], args, 0), 'memory budget exceeded')

    def test_recycled_pid_is_not_signalled_via_old_handle(self):
        backend = guard.LinuxBackend()
        backend.handles[42] = (123, 99)
        with patch.object(signal, 'pidfd_send_signal', create=True) as send:
            backend.terminate(42, 456)
        send.assert_not_called()

    def test_discovery_rejects_reused_owned_pid(self):
        backend = guard.LinuxBackend()
        replacement = guard.ProcessInfo(42, 456, "unrelated", 1, 42, 42)
        with patch.object(backend, "snapshot", return_value={42: replacement}):
            with self.assertRaises(guard.IdentityChanged):
                backend.discover(42, {42: 123})

    def test_unreaped_root_reserves_group_but_recycled_group_is_excluded(self):
        backend = object.__new__(guard.DarwinBackend)
        descendant = guard.Sample(guard.ProcessInfo(43, 456, "owned"), 1, 1)
        def listed(name, pid):
            return {43} if name == "proc_listpgrppids" else set()
        with patch.object(backend, "listed", side_effect=listed), patch.object(
                backend, "measure", side_effect=lambda pid, expected=None: descendant if pid == 43 else None):
            self.assertEqual(set(backend.discover(42, {42: 123}, root_held=True)), {43})
            self.assertEqual(backend.discover(42, {42: 123}, root_held=False), {})

    def test_darwin_exited_rusage_is_dead_despite_retained_counters(self):
        backend = object.__new__(guard.DarwinBackend)
        backend.lib = Mock()
        usage = guard.Usage(start=123, exit=456, footprint=1000, resident=2000)
        with patch.object(backend, 'usage', return_value=usage), patch.object(os, 'kill') as kill:
            sample = backend.measure(42, 123)
            backend.terminate(42, 123)
        self.assertEqual((sample.info.birth, sample.info.state, sample.footprint, sample.resident),
                         (123, 'Z', 0, 0))
        backend.lib.proc_name.assert_not_called()
        kill.assert_not_called()
        with patch.object(backend, 'usage', return_value=usage), self.assertRaises(guard.IdentityChanged):
            backend.measure(42, 999)

    def test_darwin_missing_name_requires_verified_death_and_stable_birth(self):
        backend = object.__new__(guard.DarwinBackend)
        backend.lib = Mock()
        backend.lib.proc_name.return_value = 0
        usage = guard.Usage(start=123, footprint=1000, resident=2000)
        with patch.object(backend, 'usage', return_value=usage), patch.object(
                backend, 'short_info', return_value=guard.BsdShortInfo(pid=42, status=5)):
            self.assertEqual(backend.measure(42, 123).info.state, 'Z')
        # A failed live-name lookup remains fail closed, even with zero counters.
        for footprint in (0, 1000):
            live = guard.Usage(start=123, footprint=footprint)
            with patch.object(backend, 'usage', return_value=live), patch.object(
                    backend, 'short_info', return_value=guard.BsdShortInfo(pid=42, status=2)):
                with self.assertRaisesRegex(RuntimeError, 'cannot identify live PID'):
                    backend.measure(42, 123)
        with patch.object(backend, 'usage', side_effect=[usage, guard.Usage(start=999)]), patch.object(
                backend, 'short_info', return_value=guard.BsdShortInfo(pid=42, status=5)):
            with self.assertRaises(guard.IdentityChanged):
                backend.measure(42, 123)

    def test_darwin_kill_uses_birth_even_when_live_name_is_unavailable(self):
        backend = object.__new__(guard.DarwinBackend)
        usage = guard.Usage(start=123, footprint=1000)
        with patch.object(backend, 'usage', return_value=usage), patch.object(
                backend, 'measure', side_effect=RuntimeError('unmeasurable live worker')) as measure, patch.object(
                os, 'kill') as kill:
            backend.terminate(42, 123)
            kill.assert_called_once_with(42, signal.SIGKILL)
            measure.assert_not_called()
        with patch.object(backend, 'usage', return_value=usage), patch.object(os, 'kill') as kill:
            backend.terminate(42, 999)
            kill.assert_not_called()

    def test_darwin_group_permission_error_requires_verified_dead_members(self):
        backend = object.__new__(guard.DarwinBackend)
        live = guard.Sample(guard.ProcessInfo(42, 123, 'worker'), 1000, 2000)
        dead = guard.Sample(guard.ProcessInfo(42, 123, '', state='Z'), 0, 0)
        with patch.object(backend, 'listed', return_value={42}), patch.object(
                backend, 'measure', return_value=dead), patch.object(
                os, 'killpg', side_effect=PermissionError) as kill:
            backend.terminate_group(42, {42: 123})
            kill.assert_called_once_with(42, signal.SIGKILL)
        with patch.object(backend, 'listed', return_value=set()), patch.object(
                backend, 'measure') as measure, patch.object(
                os, 'killpg', side_effect=PermissionError) as kill:
            backend.terminate_group(42, {42: 123})
            kill.assert_called_once_with(42, signal.SIGKILL)
            measure.assert_not_called()
        with patch.object(backend, 'listed', return_value={42}), patch.object(
                backend, 'measure', return_value=live), patch.object(os, 'killpg', side_effect=PermissionError):
            with self.assertRaises(PermissionError):
                backend.terminate_group(42, {42: 123})

    def test_darwin_rusage_layout_preserved(self):
        self.assertEqual(guard.Usage.resident.offset, 16 + 6 * 8)
        self.assertEqual(guard.Usage.footprint.offset, 16 + 7 * 8)
        self.assertEqual(guard.Usage.start.offset, 16 + 8 * 8)
        self.assertEqual(guard.Usage.exit.offset, 16 + 9 * 8)
        self.assertEqual(ctypes.sizeof(guard.BsdShortInfo), 64)
        self.assertEqual(guard.BsdShortInfo.status.offset, 12)
        self.assertEqual(guard.BsdShortInfo.comm.offset, 16)
        self.assertEqual(guard.LOCK_PATH, '/tmp/airbender-fv-single-worker.lock')


class ProcessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        # Never start a second worker while another task owns the global lock.
        with open(guard.LOCK_PATH, 'a+') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise RuntimeError('ProcessTests must run unwrapped with the global worker idle') from error

    def command(self, code, seconds=3):
        return [sys.executable, str(SCRIPT), '--mib', '128', '--resident-mib', '256',
                '--seconds', str(seconds), '--log', str(self.directory / 'job.log'),
                '--', sys.executable, '-c', code]

    def result(self, code, seconds=3):
        process = subprocess.run(self.command(code, seconds), capture_output=True, text=True, timeout=20)
        result = json.loads(process.stdout.strip().splitlines()[-1])
        self.assertEqual(result['live_owned_after'], [], process.stdout + process.stderr)
        self.assertTrue(result['backend'].startswith(('darwin-', 'linux-')))
        return process, result

    def marker_code(self, marker):
        return (f'import sys,os,json,time,pathlib; sys.path.insert(0,{str(SCRIPT.parent)!r}); '
                'import bounded_fv as g; b=g.select_backend(); s=b.measure(os.getpid()); '
                f'pathlib.Path({str(marker)!r}).write_text(json.dumps(dict(pid=os.getpid(),birth=s.info.birth))); '
                'b.close(); time.sleep(5)')

    def assert_gone(self, marker):
        identity = json.loads(marker.read_text())
        backend = guard.select_backend()
        try:
            measured = backend.measure(identity['pid'])
            self.assertTrue(measured is None or measured.info.birth != identity['birth'] or
                            (measured.info.state in ('Z', 'X', 'x') if not backend.adopted_children else False) or
                            (not backend.adopted_children and max(measured.footprint, measured.resident) == 0))
        finally:
            backend.close()
        return identity['pid']

    def test_exit_code_and_worker_environment(self):
        code = "import os,sys; assert all(os.environ[x]=='1' for x in ('LEAN_NUM_THREADS','OMP_NUM_THREADS','OPENBLAS_NUM_THREADS')); sys.exit(7)"
        process, result = self.result(code)
        self.assertEqual((process.returncode, result['reason'], result['exit']), (7, 'finished', 7))

    @unittest.skipUnless(sys.platform == 'linux', 'Explicit process stack setting is validated on Linux')
    def test_explicit_finite_stack_is_applied_and_recorded(self):
        command = self.command('import resource; assert resource.getrlimit(resource.RLIMIT_STACK)[0] == 32 << 20')
        command[command.index('--'):command.index('--')] = ['--stack-mib', '32']
        process = subprocess.run(command, capture_output=True, text=True, timeout=20)
        result = json.loads(process.stdout.strip().splitlines()[-1])
        self.assertEqual((process.returncode, result['reason'], result['stack_bytes']),
                         (0, 'finished', 32 << 20), process.stdout + process.stderr)

    @unittest.skipUnless(sys.platform == 'linux', 'Linux mm teardown control requires Linux')
    def test_many_short_children_exit_normally(self):
        code = ('import subprocess,sys; '
                '[subprocess.run([sys.executable,"-c","pass"],check=True) for _ in range(60)]')
        for _ in range(3):
            process, result = self.result(code, seconds=8)
            self.assertEqual((process.returncode, result['reason']), (0, 'finished'), result)

    @unittest.skipUnless(sys.platform == 'linux', 'Linux parent-death supervision requires Linux')
    def test_killed_guard_reaps_detached_payload_before_releasing_lock(self):
        marker = self.directory / 'detached.json'
        inner = self.marker_code(marker)
        code = ('import subprocess,sys,time; '
                f'subprocess.Popen([sys.executable,"-c",{inner!r}],start_new_session=True); time.sleep(10)')
        child = subprocess.Popen(self.command(code, seconds=15), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 5
            while not marker.exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(marker.exists())
            child.kill()
            child.communicate(timeout=20)
            deadline = time.monotonic() + 8
            with open(guard.LOCK_PATH, 'a+') as lock:
                while True:
                    try:
                        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        break
                    except BlockingIOError:
                        self.assertLess(time.monotonic(), deadline)
                        time.sleep(.02)
                self.assert_gone(marker)
        finally:
            if child.poll() is None:
                child.terminate()
                child.communicate(timeout=20)

    def test_timeout_reaps_setsid_descendant(self):
        marker = self.directory / 'grandchild.json'
        inner = self.marker_code(marker)
        code = (f'import subprocess,sys,time,pathlib; subprocess.Popen([sys.executable,"-c",{inner!r}],start_new_session=True); '
                f'p=pathlib.Path({str(marker)!r}); deadline=time.monotonic()+3;\nwhile not p.exists() and time.monotonic()<deadline: time.sleep(.01)\nassert p.exists(); time.sleep(5)')
        process, result = self.result(code, seconds=0.6)
        self.assertEqual(process.returncode, 125)
        self.assertEqual(result['reason'], 'wall-time budget exceeded', result)
        self.assertIn(self.assert_gone(marker), result['owned_pids'])

    @unittest.skipUnless(sys.platform == 'linux', 'Linux subreaper runtime control requires Linux CI')
    def test_quick_orphan_is_adopted_and_reaped(self):
        marker = self.directory / 'orphan.json'
        inner = self.marker_code(marker)
        code = (f'import subprocess,sys,time,pathlib; subprocess.Popen([sys.executable,"-c",{inner!r}],start_new_session=True); '
                f'p=pathlib.Path({str(marker)!r}); deadline=time.monotonic()+3;\nwhile not p.exists() and time.monotonic()<deadline: time.sleep(.01)\nassert p.exists()')
        process, result = self.result(code)
        self.assertEqual((process.returncode, result['reason']), (0, 'finished'), result)
        # The supervisor may adopt and reap it between the outer guard's
        # samples. Check the actual birth identity has gone, not sampling luck.
        self.assert_gone(marker)

    def test_lock_contention_never_launches_payload(self):
        marker = self.directory / 'must-not-exist'
        with open(guard.LOCK_PATH, 'a+') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            process, result = self.result(f'from pathlib import Path; Path({str(marker)!r}).touch()')
        self.assertEqual(process.returncode, 125)
        self.assertIn('BlockingIOError', result['reason'])
        self.assertEqual(result['owned_pids'], [])
        self.assertFalse(marker.exists())

    def test_signal_reaps_owned_payload(self):
        marker = self.directory / 'root.json'
        child = subprocess.Popen(self.command(self.marker_code(marker)), stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 5
            while not marker.exists() and child.poll() is None and time.monotonic() < deadline:
                time.sleep(.02)
            self.assertTrue(marker.exists())
            child.send_signal(signal.SIGTERM)
            output, error = child.communicate(timeout=20)
            result = json.loads(output.strip().splitlines()[-1])
            self.assertEqual(child.returncode, 125, output + error)
            self.assertIn('signal 15', result['reason'])
            self.assertEqual(result['live_owned_after'], [])
            self.assert_gone(marker)
        finally:
            if child.poll() is None:
                child.send_signal(signal.SIGTERM)
                child.communicate(timeout=20)


if __name__ == '__main__':
    unittest.main()
