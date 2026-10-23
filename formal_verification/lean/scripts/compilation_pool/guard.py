"""Opt-in compiler concurrency using the existing guard's aggregate resources.

The original serial entrypoint remains unchanged. This entrypoint changes only
its explicit Lean-process ceiling; memory, deadlines, global ownership and
process cleanup use the same backend and limits.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts import bounded_fv as serial_guard


def budget_reason(samples, args, elapsed, workers=4):
    if isinstance(workers, bool) or workers not in (1, 2, 3, 4):
        raise ValueError('Worker limit must be 1..4')
    if sum(sample.info.name == 'lean' for sample in samples) > workers:
        return 'Lean worker limit exceeded'
    if (sum(sample.footprint for sample in samples) > args.mib << 20 or
            sum(sample.resident for sample in samples) > args.resident_mib << 20):
        return 'memory budget exceeded'
    if elapsed > args.seconds:
        return 'wall-time budget exceeded'
    return None


def main(argv=None):
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--lean-workers', type=int, choices=range(1, 5), default=4)
    options, remaining = parser.parse_known_args(argv)
    observed_peak = 0
    previous = serial_guard.budget_reason

    def observe(samples, args, elapsed):
        nonlocal observed_peak
        observed_peak = max(observed_peak, sum(sample.info.name == 'lean' for sample in samples))
        return budget_reason(samples, args, elapsed, options.lean_workers)

    output = io.StringIO()
    try:
        serial_guard.budget_reason = observe
        with contextlib.redirect_stdout(output):
            code = serial_guard.main(remaining)
    finally:
        serial_guard.budget_reason = previous
    records = [json.loads(line) for line in output.getvalue().splitlines() if line.startswith('{')]
    if len(records) != 1 or 'reason' not in records[0]:
        raise RuntimeError('Aggregate guard produced no unambiguous result')
    record = records[0]
    record.update(lean_workers_limit=options.lean_workers, lean_workers_peak=observed_peak)
    print(json.dumps(record), flush=True)
    return code


if __name__ == '__main__':
    sys.exit(main())
