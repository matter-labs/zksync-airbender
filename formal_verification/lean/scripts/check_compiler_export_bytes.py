#!/usr/bin/env python3
"""Compare the exact native export inventory and bytes, excluding derived directories."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile


def compare(retained, fresh, requalify=False):
    retained_dir, fresh_dir = Path(retained), Path(fresh)
    retained = {path.name: path for path in retained_dir.iterdir() if path.is_file()}
    fresh = {path.name: path for path in fresh_dir.iterdir() if path.is_file()}
    if retained.keys() != fresh.keys():
        raise ValueError('Native compiler export file inventories differ')
    for name in sorted(retained):
        if requalify and name == 'manifest.json':
            continue
        if retained[name].read_bytes() != fresh[name].read_bytes():
            raise ValueError('Native compiler export differs: ' + name)
    if requalify:
        from check_gkr_translations import check
        # Fresh producer pins, source/sidecar bindings, certificates and native
        # circuit identities must all pass. The other 33 files matched above.
        check(fresh_dir)
        old_path, new_path = retained['manifest.json'], fresh['manifest.json']
        before = old_path.read_bytes()
        old, new = json.loads(before), json.loads(new_path.read_bytes())
        old.pop('compiler_inputs')
        new.pop('compiler_inputs')
        if old != new:
            raise ValueError('Compiler requalification may change only producer input receipts')
        with tempfile.NamedTemporaryFile(dir=retained_dir, prefix='.qualified-', delete=False) as stream:
            stream.write(new_path.read_bytes())
            temporary = Path(stream.name)
        try:
            os.replace(temporary, old_path)
        finally:
            temporary.unlink(missing_ok=True)
        check(retained_dir)
        report = {'status': 'qualified', 'payload_files': len(retained) - 1,
                  'previous_manifest_sha256': hashlib.sha256(before).hexdigest(),
                  'qualified_manifest_sha256': hashlib.sha256(old_path.read_bytes()).hexdigest()}
        (fresh_dir.parent / 'qualified-compiler-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    return len(retained)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('fresh', type=Path)
    parser.add_argument('--retained', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'artifacts/compiler')
    parser.add_argument('--requalify', action='store_true', help='Promote only changed producer pins after every payload byte and fresh provenance check passes')
    args = parser.parse_args()
    try:
        count = compare(args.retained, args.fresh, args.requalify)
    except (OSError, ValueError) as error:
        parser.exit(1, str(error) + '\n')
    print(f'PASS {count} native compiler export files reproduce byte for byte')


if __name__ == '__main__':
    main()
