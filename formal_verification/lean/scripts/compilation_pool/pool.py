"""Ready jobs inside one outer aggregate guard; no nested per-job guards.

Reservations govern admission, while the outer guard measures actual combined
use. Unknown peaks run alone. Member logs/exits are distinct from the aggregate
guard's resource receipt.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import signal
import subprocess
import time


def reservation(job):
    footprint = job.get('reserved_footprint_mib')
    resident = job.get('reserved_resident_mib')
    unknown = footprint is None or resident is None
    if unknown:
        return 2432.0, 4992.0, True
    if (isinstance(footprint, bool) or isinstance(resident, bool) or
            not math.isfinite(float(footprint)) or not math.isfinite(float(resident)) or
            not 0 < float(footprint) <= 2432 or not 0 < float(resident) <= 4992):
        raise ValueError('Invalid memory reservation')
    return (float(footprint), float(resident), bool(job.get('exclusive', False)) or
            float(footprint) > 1216 or float(resident) > 2496)


def validate_manifest(spec):
    jobs = spec['jobs']
    if not isinstance(jobs, list) or not jobs:
        raise ValueError('Require nonempty jobs')
    labels = [job['label'] for job in jobs]
    if (len(labels) != len(set(labels)) or any(not isinstance(label, str) or
            not re.fullmatch(r'[A-Za-z0-9_.-]{1,160}', label) for label in labels)):
        raise ValueError('Require unique safe job labels')
    for job in jobs:
        command = job['argv']
        if not isinstance(command, list) or not command or any(not isinstance(part, str) or '\0' in part for part in command):
            raise ValueError('Require an explicit argument vector')
        cwd = Path(job['cwd'])
        if not cwd.is_absolute() or not cwd.is_dir():
            raise ValueError('Require an existing absolute working directory')
        seconds = float(job.get('seconds', 900))
        if not math.isfinite(seconds) or not 0 < seconds <= 900:
            raise ValueError('Member deadline must be in (0, 900] seconds')
        dependencies = job.get('dependencies', [])
        if not isinstance(dependencies, list) or not set(dependencies) <= set(labels):
            raise ValueError('Unknown dependency')
        allowed = job.get('allowed_exits', [0])
        if allowed not in ([0], [0, 3]):
            raise ValueError('Only explicit cached-query exit 3 may be retained')
        if allowed == [0, 3] and command[:5] != ['lake', '--no-cache', '--no-build', '--json', 'query']:
            raise ValueError('Expected staleness is restricted to read-only Lake queries')
        reservation(job)
    pending = {job['label']: set(job.get('dependencies', [])) for job in jobs}
    while pending:
        ready = {label for label, deps in pending.items() if not deps}
        if not ready:
            raise ValueError('Cyclic job dependencies')
        pending = {label: deps - ready for label, deps in pending.items() if label not in ready}
    return jobs


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--workers', type=int, choices=range(1, 5), default=4)
    args = parser.parse_args(argv)
    if args.output.exists():
        raise ValueError('Require a fresh output directory')
    raw = args.manifest.read_bytes()
    spec = json.loads(raw)
    pending = list(validate_manifest(spec))
    args.output.mkdir(parents=True)
    active, completed, done = {}, [], set()
    peak, failure, started = 0, None, time.monotonic()
    identities = spec.get('inputs', {})

    def check_inputs():
        if args.manifest.read_bytes() != raw:
            raise ValueError('Manifest changed during execution')
        for name, expected in identities.items():
            path = Path(name)
            if not path.is_absolute() or not path.is_file():
                raise ValueError('Missing absolute input: ' + name)
            with path.open('rb') as stream:
                if hashlib.file_digest(stream, 'sha256').hexdigest() != expected:
                    raise ValueError('Input changed: ' + name)

    def state(phase):
        data = {'phase': phase, 'workers_limit': args.workers, 'concurrent_jobs_peak': peak,
                'active': list(active), 'completed': completed, 'failure': failure,
                'seconds': round(time.monotonic() - started, 3),
                'manifest_sha256': hashlib.sha256(raw).hexdigest()}
        temporary = args.output / 'state.tmp'
        temporary.write_text(json.dumps(data, indent=2) + '\n')
        temporary.replace(args.output / 'state.json')

    def interrupted(signum, _frame):
        raise InterruptedError('Signal ' + str(signum))

    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, interrupted)
    try:
        check_inputs()
        while pending or active:
            changed = False
            for label, (child, job, log, begin) in list(active.items()):
                code = child.poll()
                if code is not None:
                    log.close()
                    completed.append({'label': label, 'argv': job['argv'], 'cwd': job['cwd'],
                                      'exit': code, 'started_monotonic': begin,
                                      'seconds': round(time.monotonic() - begin, 3),
                                      'log': str(args.output / (label + '.log'))})
                    del active[label]
                    changed = True
                    if code not in job.get('allowed_exits', [0]):
                        raise RuntimeError('Member failed: ' + label + ' exit ' + str(code))
                    if code == 0:
                        done.add(label)
                elif time.monotonic() - begin > float(job.get('seconds', 900)):
                    raise TimeoutError('Member deadline exceeded: ' + label)
            while len(active) < args.workers:
                selected = None
                for job in pending:
                    if not set(job.get('dependencies', [])) <= done:
                        continue
                    footprint, resident, exclusive = reservation(job)
                    running = [reservation(item[1]) for item in active.values()]
                    if active and (exclusive or any(item[2] for item in running)):
                        continue
                    if active and (128 + footprint + sum(item[0] for item in running) > 2560 or
                                   128 + resident + sum(item[1] for item in running) > 5120):
                        continue
                    selected = job
                    break
                if selected is None:
                    break
                pending.remove(selected)
                label = selected['label']
                log = (args.output / (label + '.log')).open('w')
                begin = time.monotonic()
                child = subprocess.Popen(selected['argv'], cwd=selected['cwd'], stdout=log, stderr=subprocess.STDOUT)
                active[label] = (child, selected, log, begin)
                peak = max(peak, len(active))
                changed = True
            if pending and not active:
                raise RuntimeError('No runnable job')
            if changed:
                state('running')
            if active:
                time.sleep(.05)
        check_inputs()
        passed = all(item['exit'] == 0 for item in completed)
        state('complete' if passed else 'stale')
        result = {'passed': passed, 'workers_limit': args.workers, 'concurrent_jobs_peak': peak,
                  'jobs': completed, 'seconds': round(time.monotonic() - started, 3),
                  'manifest_sha256': hashlib.sha256(raw).hexdigest()}
        (args.output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print(('POOL_PASS ' if passed else 'POOL_STALE ') + str(len(completed)) + ' jobs; peak ' + str(peak), flush=True)
        return 0 if passed else 3
    except BaseException as error:
        failure = type(error).__name__ + ': ' + str(error)
        state('failed')
        raise
    finally:
        for child, job, log, begin in active.values():
            if child.poll() is None:
                child.terminate()
        for child, job, log, begin in active.values():
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait(timeout=5)
            if not log.closed:
                log.close()
        active.clear()
        if failure is not None:
            state('failed_reaped')


if __name__ == '__main__':
    raise SystemExit(main())
