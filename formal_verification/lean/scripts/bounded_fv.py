#!/usr/bin/env python3
"""Foreground, single-worker FV resource guard (Darwin or modern Linux).

Darwin uses the established libproc rusage-v2 footprint/RSS counters. Linux uses
an explicitly approximate charged-memory proxy from smaps_rollup, not Darwin
phys_footprint or exact memcg charging. See LinuxBackend.metric below. Both
backends sample at 50ms; transient between-sample peaks are not a hard OS limit.
Darwin follows sampled descendants and owned groups, without Linux-style orphan
adoption. A child that detaches and loses its parent between samples can escape
observation; supported FV commands wait for their compiler/export children.

Keep /tmp/airbender_bounded.py unchanged. Run this guard as the one foreground
owner, never inside another guard holding the same global lock. Replay may select
an explicit finite stack limit. No cgroup, daemon, external package or GPU
operation is created.
"""

import argparse
import ctypes
from dataclasses import dataclass, replace
import errno
import fcntl
import json
import math
import os
from pathlib import Path
import resource
import signal
import stat as stat_module
import subprocess
import sys
import time

LOCK_PATH = '/tmp/airbender-fv-single-worker.lock'
POLL_SECONDS = 0.05
CLEANUP_SECONDS = 7.0


@dataclass(frozen=True)
class ProcessInfo:
    pid: int
    birth: int
    name: str
    ppid: int = 0
    pgrp: int = 0
    session: int = 0
    state: str = ''
    argv: tuple[bytes, ...] = ()


@dataclass(frozen=True)
class Sample:
    info: ProcessInfo
    footprint: int
    resident: int
    resident_for_limit: int | None = None

    @property
    def bounded_resident(self):
        return self.resident if self.resident_for_limit is None else self.resident_for_limit


class IdentityChanged(RuntimeError):
    pass


class Usage(ctypes.Structure):
    # Exact established Darwin proc_pid_rusage(pid, RUSAGE_INFO_V2=2, ...) layout.
    _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [(n, ctypes.c_uint64) for n in (
        'user', 'system', 'idle', 'interrupts', 'pageins', 'wired', 'resident',
        'footprint', 'start', 'exit', 'child_user', 'child_system', 'child_idle',
        'child_interrupts', 'child_pageins', 'child_elapsed', 'read', 'written')]


class BsdShortInfo(ctypes.Structure):
    # SDK sys/proc_info.h proc_bsdshortinfo, PROC_PIDT_SHORTBSDINFO=13.
    # MAXCOMLEN=16; uid_t/gid_t and the remaining scalars are uint32_t.
    _fields_ = [(name, ctypes.c_uint32) for name in ('pid', 'ppid', 'pgrp', 'status')] + [
        ('comm', ctypes.c_char * 16)] + [(name, ctypes.c_uint32) for name in (
            'flags', 'uid', 'gid', 'ruid', 'rgid', 'svuid', 'svgid', 'reserved')]


class DarwinBackend:
    name = 'darwin-libproc-rusage-v2'
    metric = 'libproc phys_footprint; separate resident_size'
    adopted_children = False

    def __init__(self):
        self.lib = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
        self.lib.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
        self.lib.proc_name.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
        self.lib.proc_pidinfo.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                                          ctypes.c_void_p, ctypes.c_int]
        for name in ('proc_listchildpids', 'proc_listpgrppids'):
            getattr(self.lib, name).argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_int]

    def usage(self, pid):
        out = Usage()
        if self.lib.proc_pid_rusage(pid, 2, ctypes.byref(out)):
            error = ctypes.get_errno()
            if error == errno.ESRCH:
                return None
            raise OSError(error, f'cannot measure PID {pid}')
        return out

    def listed(self, name, pid):
        out = (ctypes.c_int * 16384)()
        size = getattr(self.lib, name)(pid, out, ctypes.sizeof(out))
        if size < 0:
            raise OSError(ctypes.get_errno(), name)
        pids = {value for value in out if value > 0}
        if len(pids) >= len(out) - 1:
            raise RuntimeError('process list capacity reached')
        return pids

    def short_info(self, pid):
        out = BsdShortInfo()
        size = self.lib.proc_pidinfo(pid, 13, 0, ctypes.byref(out), ctypes.sizeof(out))
        if size <= 0:
            error = ctypes.get_errno()
            if error == errno.ESRCH:
                return None
            raise OSError(error, f'cannot obtain BSD status for PID {pid}')
        if size != ctypes.sizeof(out) or out.pid != pid:
            raise RuntimeError(f'invalid BSD status for PID {pid}')
        return out

    def measure(self, pid, expected=None):
        measured = self.usage(pid)
        if measured is None:
            return None
        if expected is not None and measured.start != expected:
            raise IdentityChanged(f'owned PID unexpectedly reused: {pid}')

        def exited():
            # libproc can retain the last footprint/RSS on an exited process.
            # ri_proc_exit_abstime or SZOMB (sys/proc.h=5), never a missing name
            # or a zero counter alone, establishes that it cannot execute.
            return Sample(ProcessInfo(pid, measured.start, '', state='Z'), 0, 0)

        if measured.exit:
            return exited()
        name = ctypes.create_string_buffer(128)
        length = self.lib.proc_name(pid, name, len(name))
        if length <= 0:
            status = self.short_info(pid)
            after = self.usage(pid)
            if after is None:
                return None
            if after.start != measured.start:
                raise IdentityChanged(f'PID changed while checking exit status: {pid}')
            measured = after
            if measured.exit or (status is not None and status.status == 5):
                return exited()
            raise RuntimeError(f'cannot identify live PID {pid}')
        return Sample(ProcessInfo(pid, measured.start, name.value.decode(errors='replace')),
                      measured.footprint, measured.resident)

    def terminate_group(self, root, owned):
        # Caller must still hold the unreaped child identity. An all-zombie group
        # cannot execute, and Darwin may reject killpg for it with EPERM.
        def live_members():
            return [pid for pid in self.listed('proc_listpgrppids', root)
                    if (sample := self.measure(pid, owned.get(pid))) is not None
                    and sample.info.state != 'Z']
        try:
            # The held child identity authorizes this group signal even if a
            # live-name/status probe failed; cleanup must still stop that work.
            os.killpg(root, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            # Exit can race the signal. Suppress EPERM only after remeasuring
            # every remaining member and proving that none can execute.
            if live_members():
                raise

    def preflight(self):
        if signal.getsignal(signal.SIGCHLD) == signal.SIG_IGN:
            raise RuntimeError("guard requires waitable SIGCHLD disposition")
        sample = self.measure(os.getpid())
        if sample is None or sample.footprint <= 0:
            raise RuntimeError('footprint API unavailable')
        return sample.info

    def prepare_owner(self):
        if self.listed('proc_listchildpids', os.getpid()):
            raise RuntimeError('foreground guard already has unrelated children')

    def discover(self, root, owned, root_held=False):
        group = self.listed('proc_listpgrppids', root)
        # Never follow a recycled group solely because it has the old number.
        valid_group = root_held
        for pid in group & set(owned):
            current = self.measure(pid, owned[pid])
            valid_group |= current is not None
        pending = list((group if valid_group else set()) | {root} | set(owned))
        result = {}
        while pending:
            pid = pending.pop()
            if pid in result:
                continue
            current = self.measure(pid, owned.get(pid))
            if current is None:
                continue
            result[pid] = current.info
            pending.extend(self.listed('proc_listchildpids', pid) - set(result))
        return result

    def terminate(self, pid, birth):
        # Keep signalling independent of name lookup failure, so an unmeasurable
        # live worker is still stopped. This is the established immediate rusage
        # birth check; Darwin has no pidfd-style atomic check-and-signal API.
        current = self.usage(pid)
        if current is not None and current.start == birth and not current.exit:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except PermissionError:
                after = self.measure(pid, birth)
                if after is not None and after.info.state != 'Z':
                    raise

    def release_exited(self, pid):
        pass

    def reap(self, owned, root):
        pass

    def close(self):
        pass


def parse_proc_stat(source):
    """Linux stat: comm may contain spaces, newlines and closing parentheses."""
    opening, closing = source.find(' ('), source.rfind(')')
    if opening <= 0 or closing <= opening:
        raise ValueError('malformed /proc stat comm')
    pid = int(source[:opening])
    fields = source[closing + 1:].split()
    if len(fields) < 20 or len(fields[0]) != 1:
        raise ValueError('truncated /proc stat')
    ppid, pgrp, session, birth = (int(fields[index]) for index in (1, 2, 3, 19))
    # A dying task can lose its process-group/session association before its
    # stat entry disappears. Neither field is the PID's birth identity.
    if pid <= 0 or min(birth, ppid) < 0 or min(pgrp, session) < -1:
        raise ValueError('invalid /proc stat identity')
    return ProcessInfo(pid, birth, source[opening + 2:closing], ppid, pgrp, session, fields[0])


def parse_smaps_rollup(source):
    required = {'Rss', 'Anonymous', 'Pss_Shmem', 'Swap', 'Private_Hugetlb', 'Shared_Hugetlb'}
    counters = {}
    for line in source.splitlines():
        if ':' not in line:
            continue
        name, value = line.split(':', 1)
        if name not in required:
            continue
        pieces = value.split()
        if name in counters or len(pieces) != 2 or pieces[1] != 'kB' or not pieces[0].isdigit():
            raise ValueError(f'invalid or duplicate smaps_rollup counter: {name}')
        counters[name] = int(pieces[0]) * 1024
    if set(counters) != required:
        raise ValueError(f'missing smaps_rollup counters: {sorted(required - set(counters))}')
    if counters['Anonymous'] > counters['Rss'] or counters['Pss_Shmem'] > counters['Rss']:
        raise ValueError('inconsistent smaps_rollup resident counters')
    huge = counters['Private_Hugetlb'] + counters['Shared_Hugetlb']
    charged = counters['Anonymous'] + counters['Pss_Shmem'] + counters['Swap'] + huge
    return charged, counters['Rss'] + huge, charged - counters['Swap']


class LinuxBackend:
    name = 'linux-proc-smaps-rollup-pidfd-subreaper'
    metric = ('approximate charged proxy = Anonymous + Pss_Shmem + Swap + '
              'Private_Hugetlb + Shared_Hugetlb; bounded resident excludes Swap; '
              'total Rss + hugetlb is telemetry only')
    adopted_children = True

    def __init__(self, proc=Path('/proc')):
        self.proc = Path(proc)
        self.handles = {}
        self.previous_subreaper = None
        self.libc = None

    def info(self, pid):
        try:
            info = parse_proc_stat((self.proc / str(pid) / 'stat').read_text(errors='surrogateescape'))
        except (FileNotFoundError, ProcessLookupError):
            return None
        if info.pid != pid:
            raise RuntimeError(f'/proc identity mismatch: {pid}')
        if info.name == 'lean':
            try:
                with (self.proc / str(pid) / 'cmdline').open('rb') as stream:
                    command = stream.read(4096)
            except (FileNotFoundError, ProcessLookupError):
                return None
            # Unknown, empty or truncated arguments conservatively count as a
            # worker. The surrounding measurement rechecks the birth identity.
            if command.endswith(b'\0') and len(command) < 4096:
                info = replace(info, argv=tuple(command[:-1].split(b'\0')))
        return info

    def pin(self, info):
        previous = self.handles.get(info.pid)
        if previous is not None:
            if previous[0] != info.birth:
                raise IdentityChanged(f'owned PID unexpectedly reused: {info.pid}')
            return
        try:
            descriptor = os.pidfd_open(info.pid, 0)
        except ProcessLookupError:
            return
        again = self.info(info.pid)
        if again is None or again.birth != info.birth:
            os.close(descriptor)
            if again is not None:
                raise IdentityChanged(f'PID reused while pinning: {info.pid}')
            return
        self.handles[info.pid] = (info.birth, descriptor)

    def measure(self, pid, expected=None):
        info = self.info(pid)
        if info is None:
            self.release_exited(pid)
            return None
        if expected is not None and info.birth != expected:
            raise IdentityChanged(f'owned PID unexpectedly reused: {pid}')
        if info.state in ('Z', 'X', 'x'):
            self.release_exited(pid)
            return Sample(info, 0, 0)
        self.pin(info)
        try:
            memory = (self.proc / str(pid) / 'smaps_rollup').read_text()
        except (FileNotFoundError, ProcessLookupError):
            again = self.info(pid)
            if again is not None and again.birth != info.birth:
                raise IdentityChanged(f'PID reused while measuring: {pid}')
            # Linux tears down mm before publishing the zombie state. Absence
            # of smaps is therefore an exit race even if stat still says R/S.
            self.release_exited(pid)
            return None if again is None else Sample(again, 0, 0)
        again = self.info(pid)
        if again is None:
            self.release_exited(pid)
            return None
        if again.birth != info.birth:
            raise IdentityChanged(f'PID reused while measuring: {pid}')
        if again.state in ('Z', 'X', 'x'):
            self.release_exited(pid)
            return Sample(again, 0, 0)
        footprint, resident, bounded_resident = parse_smaps_rollup(memory)
        return Sample(again, footprint, resident, bounded_resident)

    def snapshot(self):
        result = {}
        for entry in self.proc.iterdir():
            if entry.name.isdigit():
                info = self.info(int(entry.name))
                if info is not None:
                    result[info.pid] = info
        return result

    def preflight(self):
        if not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
            raise RuntimeError('Linux backend requires pidfd_open/pidfd_send_signal')
        if signal.getsignal(signal.SIGCHLD) == signal.SIG_IGN:
            raise RuntimeError('guard requires waitable SIGCHLD disposition')
        sample = self.measure(os.getpid())
        if sample is None or sample.footprint <= 0 or sample.resident <= 0:
            raise RuntimeError('Linux charged-memory/RSS counters unavailable')
        self.release_exited(os.getpid())
        return sample.info

    def prepare_owner(self):
        if any(info.ppid == os.getpid() for info in self.snapshot().values()):
            raise RuntimeError('foreground guard already has unrelated children')
        self.libc = ctypes.CDLL(None, use_errno=True)
        self.libc.prctl.argtypes = [ctypes.c_int] + [ctypes.c_ulong] * 4
        self.libc.prctl.restype = ctypes.c_int
        previous = ctypes.c_int()
        if self.libc.prctl(37, ctypes.addressof(previous), 0, 0, 0):
            raise OSError(ctypes.get_errno(), 'PR_GET_CHILD_SUBREAPER failed')
        self.previous_subreaper = previous.value
        if self.libc.prctl(36, 1, 0, 0, 0):
            raise OSError(ctypes.get_errno(), 'PR_SET_CHILD_SUBREAPER failed')

    def discover(self, root, owned, root_held=False):
        snapshot = self.snapshot()
        for pid, birth in owned.items():
            if pid in snapshot and snapshot[pid].birth != birth:
                raise IdentityChanged(f'owned PID unexpectedly reused: {pid}')
        group_valid = root_held or any(pid in snapshot and snapshot[pid].birth == birth and
                          snapshot[pid].pgrp == root and snapshot[pid].session == root
                          for pid, birth in owned.items())
        selected = {pid for pid in owned if pid in snapshot}
        selected.update(pid for pid, info in snapshot.items() if info.ppid == os.getpid())
        if group_valid:
            selected.update(pid for pid, info in snapshot.items()
                            if info.pgrp == root and info.session == root)
        while True:
            descendants = {pid for pid, info in snapshot.items() if info.ppid in selected}
            if descendants <= selected:
                break
            selected.update(descendants)
        return {pid: snapshot[pid] for pid in selected}

    def terminate(self, pid, birth, signum=signal.SIGKILL):
        handle = self.handles.get(pid)
        if handle is None:
            info = self.info(pid)
            if info is None or info.birth != birth or info.state in ('Z', 'X', 'x'):
                return
            self.pin(info)
            handle = self.handles.get(pid)
        if handle is not None and handle[0] == birth:
            try:
                signal.pidfd_send_signal(handle[1], signum, None, 0)
            except ProcessLookupError:
                self.release_exited(pid)

    def release_exited(self, pid):
        handle = self.handles.pop(pid, None)
        if handle is not None:
            os.close(handle[1])

    def reap(self, owned, root):
        for pid in owned:
            if pid == root:
                continue
            try:
                waited, _ = os.waitpid(pid, os.WNOHANG)
                if waited:
                    self.release_exited(pid)
            except ChildProcessError:
                pass

    def close(self):
        for pid in list(self.handles):
            self.release_exited(pid)
        if self.previous_subreaper is not None:
            if self.libc.prctl(36, self.previous_subreaper, 0, 0, 0):
                raise OSError(ctypes.get_errno(), 'restoring child-subreaper state failed')


def select_backend():
    if sys.platform == 'darwin':
        return DarwinBackend()
    if sys.platform == 'linux':
        return LinuxBackend()
    raise RuntimeError(f'unsupported resource backend: {sys.platform}')


class Tracker:
    def __init__(self, backend, root, root_held=lambda: False):
        self.backend, self.root, self.owned, self.samples = backend, root, {}, {}
        self.root_held = root_held
    def capture_root(self):
        first = self.backend.measure(self.root)
        if first is None:
            raise RuntimeError('new owned root vanished before identity capture')
        self.owned[self.root] = first.info.birth
        self.samples[self.root] = first

    def observe(self):
        samples = {}
        for pid, info in self.backend.discover(self.root, self.owned, self.root_held()).items():
            if pid in self.owned and self.owned[pid] != info.birth:
                raise IdentityChanged(f'owned PID unexpectedly reused: {pid}')
            self.owned[pid] = info.birth
            measured = self.backend.measure(pid, info.birth)
            if measured is not None:
                samples[pid] = measured
        for pid in set(self.owned) - set(samples):
            self.backend.release_exited(pid)
        self.samples = samples
        return list(samples.values())


def lean_worker_count(samples):
    # Mathlib's Cache.IO initializer invokes this read-only query from inside
    # the compiler. Linux exposes its exact argv; other/unknown invocations
    # remain workers. Every process still contributes to memory and deadlines.
    return sum(sample.info.name == 'lean' and not (
        len(sample.info.argv) == 2
        and sample.info.argv[0].rsplit(b'/', 1)[-1] == b'lean'
        and sample.info.argv[1] == b'--print-prefix') for sample in samples)


def budget_reason(samples, args, elapsed):
    if lean_worker_count(samples) > 1:
        return 'more than one Lean worker'
    if (sum(sample.footprint for sample in samples) > args.mib << 20 or
            sum(sample.bounded_resident for sample in samples) > args.resident_mib << 20):
        return 'memory budget exceeded'
    if elapsed > args.seconds:
        return 'wall-time budget exceeded'
    return None


def cleanup(child, tracker, backend, preserve_supervisor=False):
    errors = []
    deadline = time.monotonic() + CLEANUP_SECONDS
    live = []
    while True:
        try:
            tracker.observe()
        except BaseException as error:
            errors.append(f'discovery: {type(error).__name__}: {error}')
        if not backend.adopted_children and child.returncode is None:
            # An unpolled child reserves its PID even after exit. Never use this
            # group-number operation once poll/wait has reaped the leader.
            try:
                backend.terminate_group(child.pid, tracker.owned)
            except BaseException as error:
                errors.append(f"owned group kill: {type(error).__name__}: {error}")
        for pid, birth in list(tracker.owned.items()):
            try:
                if preserve_supervisor and pid == child.pid:
                    backend.terminate(pid, birth, signal.SIGTERM)
                else:
                    backend.terminate(pid, birth)
            except BaseException as error:
                errors.append(f'kill {pid}: {type(error).__name__}: {error}')
        child.poll()
        try:
            backend.reap(tracker.owned, child.pid)
            tracker.observe()
            live = [pid for pid, sample in tracker.samples.items()
                    if (sample.info.state not in ('Z', 'X', 'x') if backend.adopted_children
                        else sample.info.state != 'Z' and max(sample.footprint, sample.resident) > 0)]
            zombies = [pid for pid, sample in tracker.samples.items()
                       if backend.adopted_children and sample.info.state in ('Z', 'X', 'x')]
            if child.returncode is not None and not live and not zombies:
                break
        except BaseException as error:
            errors.append(f'verify: {type(error).__name__}: {error}')
        if time.monotonic() >= deadline:
            errors.append('owned-child cleanup could not be verified before deadline')
            break
        time.sleep(0.02)
    return live, errors


def linux_payload_owner(owner, command):
    """Hold the inherited lock and reap the payload even if the guard is killed.

    This supervisor owns no resource policy and never acquires another lock.
    Its subreaper also catches detached descendants when their parents die.
    """
    backend = LinuxBackend()
    child, tracker = None, None
    interrupted = False
    def stop(_signum, _frame):
        nonlocal interrupted
        interrupted = True
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    signal.signal(signal.SIGHUP, stop)
    backend.prepare_owner()
    def finish():
        # A D-state descendant may survive SIGKILL beyond the cleanup deadline.
        # Keep this supervisor and its lock alive until ownership is verifiable.
        while True:
            live, errors = cleanup(child, tracker, backend)
            if not live and not errors:
                return
            time.sleep(POLL_SECONDS)
    try:
        # PR_SET_PDEATHSIG is not inherited across fork. Set it in the actual
        # surviving supervisor, then check the parent to close the startup race.
        if backend.libc.prctl(1, signal.SIGTERM, 0, 0, 0):
            raise OSError(ctypes.get_errno(), 'PR_SET_PDEATHSIG failed')
        if os.getppid() != owner:
            return 125
        child = subprocess.Popen(command, start_new_session=True)
        tracker = Tracker(backend, child.pid, root_held=lambda: child.returncode is None)
        tracker.capture_root()
        while not interrupted:
            tracker.observe()
            if child.poll() is not None:
                break
            time.sleep(POLL_SECONDS)
        returncode = child.returncode
        finish()
        return returncode if not interrupted and returncode is not None and returncode >= 0 else 125
    finally:
        if child is not None and (tracker is None or child.returncode is None):
            if tracker is not None:
                finish()
            else:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.wait()
        backend.close()


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mib', type=int, required=True)
    parser.add_argument('--seconds', type=float, required=True)
    parser.add_argument('--resident-mib', type=int, default=4096)
    parser.add_argument('--log', required=True)
    parser.add_argument('--review', action='store_true', help='Allow review jobs above 900s, up to 1800s')
    parser.add_argument('--stack-mib', type=int, help='Explicit finite child stack, 8..256 MiB')
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    args.command = args.command[1:] if args.command[:1] == ['--'] else args.command
    maximum = 1800 if args.review else 900
    if (not args.command or not 8 <= args.mib <= 2560 or
            not args.mib <= args.resident_mib <= 5120 or
            not math.isfinite(args.seconds) or not 0 < args.seconds <= maximum or
            (args.stack_mib is not None and not 8 <= args.stack_mib <= 256)):
        parser.error('require command, footprint 8..2560 MiB, resident <=5120 MiB, normal 0..900s; --review permits up to 1800s')
    return args


def main(argv=None):
    args = parse_args(argv)
    started = time.monotonic()
    backend, child, tracker, lock = None, None, None, None
    reason, live, code = 'finished', [], 125
    peak = footprint_peak = resident_peak = bounded_resident_peak = 0
    try:
        backend = select_backend()
        own_info = backend.preflight()
        descriptor = os.open(LOCK_PATH, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
        metadata = os.fstat(descriptor)
        if not stat_module.S_ISREG(metadata.st_mode) or metadata.st_uid != os.getuid():
            os.close(descriptor)
            raise RuntimeError('global worker lock is not an owned regular file')
        lock = os.fdopen(descriptor, 'r+')
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        lock.seek(0)
        lock.truncate()
        json.dump({'guard_pid': os.getpid(), 'birth': own_info.birth,
                   'backend': backend.name, 'log': args.log}, lock)
        lock.flush()
        backend.prepare_owner()
        def limits():
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            if args.stack_mib is not None:
                requested = args.stack_mib << 20
                _, hard = resource.getrlimit(resource.RLIMIT_STACK)
                resource.setrlimit(resource.RLIMIT_STACK, (requested, hard))
        def interrupted(signum, frame):
            raise InterruptedError(f'signal {signum}')
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(sig, interrupted)
        environment = dict(os.environ, LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
        command = args.command
        if backend.adopted_children:
            command = [sys.executable, str(Path(__file__).resolve()), '--payload-owner', str(os.getpid()), *command]
        with open(args.log, 'wb') as output:
            child = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                     env=environment, start_new_session=True, preexec_fn=limits,
                                     pass_fds=(lock.fileno(),))
            tracker = Tracker(backend, child.pid, root_held=lambda: child.returncode is None)
            tracker.capture_root()
            while True:
                samples = tracker.observe()
                peak = max(peak, sum(max(item.footprint, item.resident) for item in samples))
                footprint_peak = max(footprint_peak, sum(item.footprint for item in samples))
                resident_peak = max(resident_peak, sum(item.resident for item in samples))
                bounded_resident_peak = max(bounded_resident_peak, sum(item.bounded_resident for item in samples))
                failure = budget_reason(samples, args, time.monotonic() - started)
                if failure:
                    reason = failure
                    break
                if child.poll() is not None:
                    break
                time.sleep(POLL_SECONDS)
    except BaseException as error:
        reason = f'guard failure: {type(error).__name__}: {error}'
    finally:
        for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
            signal.signal(sig, signal.SIG_IGN)
        if child is not None:
            if tracker is not None:
                capture_errors = []
                if child.pid not in tracker.owned and child.returncode is None:
                    # The unpolled child still reserves its PID on capture failure.
                    try:
                        if backend.adopted_children:
                            os.kill(child.pid, signal.SIGTERM)
                        else:
                            backend.terminate_group(child.pid, tracker.owned)
                    except ProcessLookupError:
                        pass
                    except BaseException as error:
                        capture_errors.append(f'initial owned group kill: {error}')
                live, errors = cleanup(child, tracker, backend, preserve_supervisor=backend.adopted_children)
                errors = capture_errors + errors
                if errors:
                    reason = f'ERROR owned cleanup unverifiable: {errors[-3:]}'
            else:
                # Before the first poll/wait the child PID cannot be recycled.
                # Kill only its newly created group while that identity is held.
                try:
                    if backend.adopted_children:
                        os.kill(child.pid, signal.SIGTERM)
                    else:
                        backend.terminate_group(child.pid, {})
                    child.wait(timeout=5)
                except BaseException as error:
                    reason = f'ERROR initial owned cleanup failed: {error}'
            code = child.returncode
        if backend is not None:
            try:
                backend.close()
            except BaseException as error:
                reason = f'ERROR backend cleanup failed: {error}'
        if lock is not None:
            lock.close()
    result = {'reason': reason, 'exit': code, 'peak_mib': round(peak / 2**20, 2),
              'footprint_peak_mib': round(footprint_peak / 2**20, 2),
              'resident_peak_mib': round(resident_peak / 2**20, 2),
              'bounded_resident_peak_mib': round(bounded_resident_peak / 2**20, 2),
              'seconds': round(time.monotonic() - started, 2),
              'owned_pids': list(tracker.owned) if tracker is not None else [],
              'live_owned_after': live, 'log': args.log,
              'backend': backend.name if backend is not None else 'unavailable',
              'footprint_metric': backend.metric if backend is not None else 'unavailable',
              'sampling_seconds': POLL_SECONDS}
    result['stack_bytes'] = args.stack_mib << 20 if args.stack_mib is not None else resource.getrlimit(resource.RLIMIT_STACK)[0]
    print(json.dumps(result), flush=True)
    return code if reason == 'finished' and code is not None and code >= 0 else 125


if __name__ == '__main__':
    if sys.argv[1:2] == ['--payload-owner'] and sys.platform == 'linux':
        sys.exit(linux_payload_owner(int(sys.argv[2]), sys.argv[3:]))
    sys.exit(main())
