#!/usr/bin/env python3
"""Qualify the explicit native-artifact budget; never change Lean guard defaults."""
import argparse
import json
from pathlib import Path
import sys

FOOTPRINT_MIB = 8192
RESIDENT_MIB = 12288
HEADROOM_MIB = 2048
MIB = 1 << 20


def qualify(total_bytes, available_bytes, cgroups=()):
    capacity, available = total_bytes, available_bytes
    for measurement in cgroups:
        maximum, current, *cache = measurement
        reclaimable = cache[0] if cache else 0
        if maximum <= 0 or current < 0 or not 0 <= reclaimable <= current:
            raise ValueError("Invalid cgroup memory measurement")
        capacity = min(capacity, maximum)
        # Cache restoration charges reclaimable file pages to a cgroup. Counting
        # inactive file cache as permanently occupied would falsely reject it.
        available = min(available, max(0, maximum - current + reclaimable))
    required = (RESIDENT_MIB + HEADROOM_MIB) * MIB
    report = {"native_footprint_mib": FOOTPRINT_MIB, "native_resident_mib": RESIDENT_MIB,
              "lean_footprint_mib": 2560, "lean_resident_mib": 5120,
              "required_available_mib": required // MIB,
              "effective_capacity_mib": capacity // MIB, "available_mib": available // MIB,
              "qualified": capacity >= required and available >= required}
    return report


def inspect(proc=Path('/proc'), cgroup=Path('/sys/fs/cgroup')):
    values = {}
    for line in (proc / 'meminfo').read_text().splitlines():
        name, _, value = line.partition(':')
        if name in ('MemTotal', 'MemAvailable'):
            amount, unit = value.split()
            if unit != 'kB':
                raise ValueError("Unexpected /proc/meminfo unit")
            values[name] = int(amount) * 1024
    limits = []
    # The visible cgroup root can be the job's own namespace. Read every visible
    # ancestor of its membership as well, so a parent hard limit is not ignored.
    directories = {cgroup}
    for line in (proc / 'self/cgroup').read_text().splitlines():
        hierarchy, controllers, relative = line.split(':', 2)
        if hierarchy == '0' or 'memory' in controllers.split(','):
            base = cgroup if hierarchy == '0' else cgroup / 'memory'
            path = (base / relative.lstrip('/')).resolve()
            if path.is_relative_to(base.resolve()):
                directories.update([path, *[p for p in path.parents if p.is_relative_to(base.resolve())]])
            directories.add(base)
    for directory in directories:
        for max_name, current_name in (('memory.max', 'memory.current'),
                                       ('memory.limit_in_bytes', 'memory.usage_in_bytes')):
            path = directory / max_name
            if not path.exists():
                continue
            raw = path.read_text().strip()
            if raw != 'max':
                current = int((directory / current_name).read_text().strip())
                stat = directory / 'memory.stat'
                stats = dict(line.split() for line in stat.read_text().splitlines()) if stat.exists() else {}
                reclaimable = int(stats.get('total_inactive_file', stats.get('inactive_file', 0)))
                limits.append((int(raw), current, min(current, reclaimable)))
    return qualify(values['MemTotal'], values['MemAvailable'], limits)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    if sys.platform != 'linux':
        raise SystemExit('Native capacity qualification requires Linux')
    report = inspect()
    args.report.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, sort_keys=True), flush=True)
    if not report['qualified']:
        raise SystemExit('Native artifact worker needs at least 14 GiB effective capacity and available memory')


if __name__ == '__main__':
    main()
