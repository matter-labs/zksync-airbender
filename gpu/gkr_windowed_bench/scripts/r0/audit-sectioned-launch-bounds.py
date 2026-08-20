#!/usr/bin/env python3
"""Stream static resource and SASS facts for the sectioned launch-bound sweep."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
from typing import Any, Iterable


RESOURCE_HEADER = re.compile(r"^\s*Function\s+(?::\s*)?([^:]+):\s*$")
SASS_HEADER = re.compile(r"^\s*Function\s*:\s*(\S+)\s*$")
RESOURCE_FACTS = re.compile(r"REG:(\d+)\s+STACK:(\d+)\s+SHARED:(\d+)\s+LOCAL:(\d+)")
OPCODES = (
    "LDC", "LDCU", "LDG", "LDL", "STL", "LDS", "STS", "CALL", "RET",
    "BSSY", "BSYNC",
)
GENERIC_SYMBOL = "ab_gkr_windowed_r0_cta288_pair_kernel"
BOUND_BUCKETS = {7: 96, 8: 80, 9: 72, 10: 64, 12: 56, 16: 40}


def consume_resources(
    lines: Iterable[str], wanted_symbols: set[str],
) -> dict[str, dict[str, int]]:
    result: dict[str, dict[str, int]] = {}
    current: str | None = None
    for raw in lines:
        match = RESOURCE_HEADER.match(raw.rstrip("\n"))
        if match:
            current = match.group(1).strip()
            if current in wanted_symbols and current in result:
                raise ValueError(f"duplicate requested resource symbol {current}")
            continue
        if current not in wanted_symbols:
            continue
        facts = RESOURCE_FACTS.search(raw)
        if facts:
            if current in result:
                raise ValueError(f"duplicate requested resource row {current}")
            registers, stack_bytes, shared_bytes, local_bytes = map(int, facts.groups())
            result[current] = {
                "registers": registers,
                "stack_bytes": stack_bytes,
                "shared_bytes": shared_bytes,
                "local_bytes": local_bytes,
            }
    missing = wanted_symbols - result.keys()
    if missing:
        raise ValueError(f"missing requested resource symbols: {sorted(missing)}")
    return result


def consume_sass(
    lines: Iterable[str], wanted_symbols: set[str],
) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    current: str | None = None
    digest: Any = None
    instructions = 0
    counts: dict[str, int] = {}

    def flush() -> None:
        nonlocal current, digest, instructions, counts
        if current not in wanted_symbols:
            return
        if current in result:
            raise ValueError(f"duplicate requested SASS symbol {current}")
        result[current] = {
            "sass_sha256": digest.hexdigest(),
            "instructions": instructions,
            **{f"opcode_{opcode.lower()}": counts[opcode] for opcode in OPCODES},
        }

    for raw in lines:
        line = raw.rstrip("\n")
        match = SASS_HEADER.match(line)
        if match:
            flush()
            current = match.group(1)
            digest = hashlib.sha256()
            instructions = 0
            counts = {opcode: 0 for opcode in OPCODES}
            continue
        if current not in wanted_symbols:
            continue
        digest.update((line + "\n").encode())
        if re.search(r"/\*[0-9a-fA-F]+\*/", line):
            instructions += 1
            opcode_match = re.search(r"\*/\s*(?:@[!A-Za-z0-9_.]+\s+)?([A-Z][A-Z0-9.]*)", line)
            if opcode_match:
                base = opcode_match.group(1).split(".", 1)[0]
                if base in counts:
                    counts[base] += 1
    flush()
    missing = wanted_symbols - result.keys()
    if missing:
        raise ValueError(f"missing requested SASS symbols: {sorted(missing)}")
    return result


def theoretical_register_bucket(geometry: str, min_blocks: int | None) -> int | None:
    if geometry == "wide9":
        return {3: 72, 4: 56}.get(min_blocks)
    return BOUND_BUCKETS.get(min_blocks)


def audit(manifest_path: pathlib.Path, elf: pathlib.Path, output: pathlib.Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    symbols = manifest["symbols"]
    expected_symbols = {2: 225, 3: 240}.get(manifest.get("schema_version"))
    if expected_symbols is None or len(symbols) != expected_symbols:
        raise ValueError("sectioned static audit requires an exact schema-v2/v3 manifest")
    include_generic = manifest.get("generic_reference_build") is not None
    wanted = {row["symbol"] for row in symbols}
    if include_generic:
        wanted.add(GENERIC_SYMBOL)
    if len(wanted) != expected_symbols + int(include_generic):
        raise ValueError("sectioned static audit symbol identities are not unique")

    resource_process = subprocess.Popen(
        ["cuobjdump", "--dump-resource-usage", str(elf)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    assert resource_process.stdout is not None
    resources = consume_resources(resource_process.stdout, wanted)
    resource_stderr = resource_process.stderr.read() if resource_process.stderr else ""
    if resource_process.wait() != 0:
        raise ValueError(f"cuobjdump resource extraction failed: {resource_stderr}")

    sass_process = subprocess.Popen(
        ["cuobjdump", "--dump-sass", str(elf)],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    )
    assert sass_process.stdout is not None
    sass = consume_sass(sass_process.stdout, wanted)
    sass_stderr = sass_process.stderr.read() if sass_process.stderr else ""
    if sass_process.wait() != 0:
        raise ValueError(f"cuobjdump SASS extraction failed: {sass_stderr}")

    rows = []
    for symbol in symbols:
        name = symbol["symbol"]
        row = {
            "version": 1,
            "arm_kind": "sectioned",
            **symbol,
            **resources[name],
            **sass[name],
            "theoretical_register_bucket": theoretical_register_bucket(
                symbol["geometry"], symbol.get("min_blocks")
            ),
        }
        rows.append(row)
    if include_generic:
        rows.append({
            "version": 1, "arm_kind": "generic", "candidate_id": "generic/reference",
            "symbol": GENERIC_SYMBOL, "shape_bits": None, "geometry": "cta288_pair",
            "min_blocks": None, "theoretical_register_bucket": None,
            **resources[GENERIC_SYMBOL], **sass[GENERIC_SYMBOL],
        })

    by_key = {(row["shape_bits"], row["geometry"], row.get("min_blocks")): row
              for row in rows if row["arm_kind"] == "sectioned"}
    for row in rows:
        if row["arm_kind"] == "generic":
            row["identical_to_natural"] = True
            continue
        natural_bound = 3 if row["geometry"] == "wide9" else None
        natural = by_key[(row["shape_bits"], row["geometry"], natural_bound)]
        row["identical_to_natural"] = row["sass_sha256"] == natural["sass_sha256"]

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(
        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in rows
    ))


def self_test() -> None:
    assert theoretical_register_bucket("wide9", 3) == 72
    assert theoretical_register_bucket("wide9", 4) == 56
    wanted = {"wanted_a", "wanted_b"}
    resources = consume_resources(iter([
        "preamble\n", " Function wanted_a:\n", " REG:55 STACK:1 SHARED:2 LOCAL:3\n",
        " Function unrelated:\n", " REG:99 STACK:9 SHARED:9 LOCAL:9\n",
        "Function wanted_b:\n", "  REG:64 STACK:0 SHARED:0 LOCAL:0 CONSTANT[0]:1\n",
    ]), wanted)
    assert resources == {
        "wanted_a": {"registers": 55, "stack_bytes": 1, "shared_bytes": 2, "local_bytes": 3},
        "wanted_b": {"registers": 64, "stack_bytes": 0, "shared_bytes": 0, "local_bytes": 0},
    }
    sass = consume_sass(iter([
        "Function : wanted_a\n", " /*0000*/ LDC R0, c[0x0][0x0];\n",
        " /*0010*/ LDL R1, [R2];\n", "Function : unrelated\n", " /*0*/ CALL X;\n",
        "Function : wanted_b\n", " /*0000*/ LDCU R0, c[0x0][0x0];\n",
        " /*0010*/ LDG R1, [R2];\n", " /*0020*/ STL [R2], R1;\n",
        " /*0030*/ LDS R1, [R2];\n", " /*0040*/ STS [R2], R1;\n",
        " /*0050*/ CALL X;\n", " /*0060*/ RET;\n",
        " /*0070*/ BSSY B0, 0x20;\n", " /*0080*/ BSYNC B0;\n",
    ]), wanted)
    assert sass["wanted_a"]["instructions"] == 2
    assert sass["wanted_a"]["opcode_ldc"] == 1 and sass["wanted_a"]["opcode_ldl"] == 1
    assert sass["wanted_b"]["instructions"] == 9
    assert [sass["wanted_b"][f"opcode_{name}"] for name in
            ("ldcu", "ldg", "stl", "lds", "sts", "call", "ret")] == [1] * 7
    assert sass["wanted_b"]["opcode_bssy"] == 1
    assert sass["wanted_b"]["opcode_bsync"] == 1
    equal_bodies = consume_sass(iter([
        "Function : wanted_a\n", " /*0000*/ RET;\n",
        "Function : wanted_b\n", " /*0000*/ RET;\n",
    ]), wanted)
    assert equal_bodies["wanted_a"]["sass_sha256"] == equal_bodies["wanted_b"]["sass_sha256"]
    for parser, lines in (
        (consume_resources, ["Function wanted_a:\n", "REG:1 STACK:0 SHARED:0 LOCAL:0\n"]),
        (consume_sass, ["Function : wanted_a\n", " /*0*/ RET;\n"]),
    ):
        try:
            parser(iter(lines), wanted)
        except ValueError as error:
            assert "missing" in str(error)
        else:
            raise AssertionError("missing requested symbol unexpectedly passed")
    try:
        consume_sass(iter(["Function : wanted_a\n", " /*0*/ RET;\n",
                           "Function : wanted_a\n", " /*0*/ RET;\n",
                           "Function : wanted_b\n", " /*0*/ RET;\n"]), wanted)
    except ValueError as error:
        assert "duplicate" in str(error)
    else:
        raise AssertionError("duplicate requested symbol unexpectedly passed")
    print("R0_SECTIONED_STATIC_FIXTURES_OK")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=pathlib.Path)
    parser.add_argument("--elf", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if None in (args.manifest, args.elf, args.output):
        parser.error("--manifest, --elf, and --output are required")
    audit(args.manifest.resolve(), args.elf.resolve(), args.output.resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
