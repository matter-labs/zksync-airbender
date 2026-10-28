#!/usr/bin/env python3
"""Compare the exact native export inventory and bytes, excluding derived directories."""
import argparse
from pathlib import Path


def compare(retained, fresh):
    retained = {path.name: path for path in Path(retained).iterdir() if path.is_file()}
    fresh = {path.name: path for path in Path(fresh).iterdir() if path.is_file()}
    if retained.keys() != fresh.keys():
        raise ValueError('Native compiler export file inventories differ')
    for name in sorted(retained):
        if retained[name].read_bytes() != fresh[name].read_bytes():
            raise ValueError('Native compiler export differs: ' + name)
    return len(retained)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('fresh', type=Path)
    parser.add_argument('--retained', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'artifacts/compiler')
    args = parser.parse_args()
    try:
        count = compare(args.retained, args.fresh)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + '\n')
    print(f'PASS {count} native compiler export files reproduce byte for byte')


if __name__ == '__main__':
    main()
