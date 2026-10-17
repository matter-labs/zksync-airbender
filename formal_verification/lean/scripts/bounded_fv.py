#!/usr/bin/env python3
"""macOS foreground verification guard. Deliberately fail closed."""
import argparse, ctypes, errno, fcntl, json, os, resource, signal, subprocess, sys, time
from pathlib import Path

class Usage(ctypes.Structure):
    _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [(n, ctypes.c_uint64) for n in (
        'user', 'system', 'idle', 'interrupts', 'pageins', 'wired', 'resident',
        'footprint', 'start', 'exit', 'child_user', 'child_system', 'child_idle',
        'child_interrupts', 'child_pageins', 'child_elapsed', 'read', 'written')]
lib = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
lib.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
lib.proc_name.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_uint32]
for name in ('proc_listchildpids', 'proc_listpgrppids'):
    getattr(lib, name).argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_int]

def usage(pid):
    out = Usage()
    if lib.proc_pid_rusage(pid, 2, ctypes.byref(out)):
        err = ctypes.get_errno()
        if err == errno.ESRCH:
            return None
        raise OSError(err, f'cannot measure PID {pid}')
    return out

def listed(name, pid):
    out = (ctypes.c_int * 16384)()
    n = getattr(lib, name)(pid, out, ctypes.sizeof(out))
    if n < 0:
        raise OSError(ctypes.get_errno(), name)
    pids = {v for v in out if v > 0}
    if len(pids) >= len(out) - 1:
        raise RuntimeError('process list capacity reached')
    return pids

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--mib', type=int, required=True)
    p.add_argument('--seconds', type=float, required=True)
    p.add_argument('--resident-mib', type=int, default=4096)
    p.add_argument('--log', required=True)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    cmd = a.command[1:] if a.command[:1] == ['--'] else a.command
    if not cmd or not 8 <= a.mib <= 3072 or not a.mib <= a.resident_mib <= 5120 or not 0 < a.seconds <= 1800:
        p.error('require command, footprint 8..3072 MiB, resident <=5120 MiB, 0..1800 seconds')
    # Cross-check the API before launching any owned work.
    if not usage(os.getpid()).footprint > 0:
        raise RuntimeError('footprint API unavailable')
    lock = open('/tmp/airbender-fv-single-worker.lock', 'a+')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    lock.seek(0)
    lock.truncate()
    json.dump({'guard_pid': os.getpid(), 'birth': usage(os.getpid()).start, 'log': a.log}, lock)
    lock.flush()
    def limits():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    env = dict(os.environ, LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1')
    peak = 0
    footprint_peak = 0
    resident_peak = 0
    reason = 'finished'
    owned = {}
    child = None
    started = time.monotonic()
    def interrupted(signum, frame):
        raise InterruptedError(f'signal {signum}')
    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, interrupted)
    with open(a.log, 'wb') as output:
        try:
            child = subprocess.Popen(cmd, stdout=output, stderr=subprocess.STDOUT,
                                     env=env, start_new_session=True, preexec_fn=limits)
            while True:
                pending = list(listed('proc_listpgrppids', child.pid) | {child.pid} | set(owned))
                seen = set()
                total = 0
                lean_workers = 0
                footprint = 0
                resident = 0
                while pending:
                    pid = pending.pop()
                    if pid in seen:
                        continue
                    seen.add(pid)
                    stat = usage(pid)
                    if stat is None:
                        continue
                    if pid in owned and owned[pid] != stat.start:
                        raise RuntimeError('owned PID unexpectedly reused')
                    owned[pid] = stat.start
                    name = ctypes.create_string_buffer(128)
                    lib.proc_name(pid, name, len(name))
                    lean_workers += int(name.value == b'lean')
                    total += max(stat.footprint, stat.resident)
                    footprint += stat.footprint
                    resident += stat.resident
                    pending.extend(listed('proc_listchildpids', pid) - seen)
                peak = max(peak, total)
                footprint_peak = max(footprint_peak, footprint)
                resident_peak = max(resident_peak, resident)
                if lean_workers > 1:
                    reason = 'more than one Lean worker'
                    break
                if footprint > a.mib << 20 or resident > a.resident_mib << 20:
                    reason = 'memory budget exceeded'
                    break
                if time.monotonic() - started > a.seconds:
                    reason = 'wall-time budget exceeded'
                    break
                if child.poll() is not None:
                    break
                time.sleep(0.05)
        except BaseException as exc:
            reason = f'guard failure: {type(exc).__name__}: {exc}'
        finally:
            if child is not None:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                # Kill observed descendants even if they changed process group.
                for pid, birth in owned.items():
                    stat = usage(pid)
                    if stat is not None and stat.start == birth:
                        try:
                            os.kill(pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                child.wait(timeout=5)
                # A process may remain briefly as a reparented zombie; it has no
                # footprint and cannot execute. Any live owned process is failure.
                for attempt in range(100):
                    live = []
                    for pid, birth in owned.items():
                        stat = usage(pid)
                        if stat and stat.start == birth and max(stat.footprint, stat.resident):
                            live.append(pid)
                    if not live:
                        break
                    time.sleep(0.02)
                if live:
                    reason = f'ERROR owned processes survived: {live}'
    code = child.returncode if child is not None else 125
    result = {'reason': reason, 'exit': code, 'peak_mib': round(peak / 2**20, 2),
              'footprint_peak_mib': round(footprint_peak / 2**20, 2),
              'resident_peak_mib': round(resident_peak / 2**20, 2),
              'seconds': round(time.monotonic() - started, 2), 'owned_pids': list(owned),
              'live_owned_after': live if child is not None else [], 'log': a.log}
    print(json.dumps(result), flush=True)
    return code if reason == 'finished' and code is not None and code >= 0 else 125

if __name__ == '__main__':
    sys.exit(main())
