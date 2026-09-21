#!/usr/bin/env python3
"""Check batch count, IDs and emitted proof files."""

import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output_dir", type=Path)
parser.add_argument("--expected-items", type=int, required=True)
parser.add_argument("--batch-id-base", type=int, default=0)
args = parser.parse_args()
assert args.expected_items > 0, "expected-items must be positive"
items = json.loads((args.output_dir / "batch_summary.json").read_text())["items"]
assert len(items) == args.expected_items, f"expected {args.expected_items} items, got {len(items)}"
expected_ids = list(range(args.batch_id_base, args.batch_id_base + args.expected_items))
assert [item["batch_id"] for item in items] == expected_ids, "unexpected batch IDs"
for item in items:
    proof = args.output_dir / item["output_file"]
    assert proof.is_file() and proof.stat().st_size > 0, f"missing or empty proof: {proof}"
print(f"validated {len(items)} batch proofs")
