#!/usr/bin/env python3
"""Compare compiled Lean public-text decoder rows with native Rust setup rows.

The comparison covers every padded decoder row, including unsupported words.
The Lean oracle emits active rows; the checker verifies that every other native
row is the out-of-range sentinel. The importer/Rust-model boundary remains a
differential test, not a kernel proof.
"""

import argparse
import bisect
import csv
import hashlib
import json
import pathlib
import struct
import subprocess
import tempfile

POOLED_FAMILIES = ("add-sub", "jump-branch", "shift-binop", "word-memory", "mul-div", "subword-memory")
REDUCED_FAMILIES = POOLED_FAMILIES[:4]
FAMILIES = POOLED_FAMILIES + ("unified",)
SMALL_PROGRAMS = {
    "one": (0x13, 0x00408093, 0x6F, 0x007181B3),
    "two": (0x13, 0x00408113, 0x6F, 0x007181B3),
    "blake-caller": (0x7C701073,) * 7 + (0x13,),
    "split-keccak": tuple(
        ((0x7CD if index == 360 or index % 15 < 5 else
          0x7CC if index % 15 < 10 else 0x7CE) << 20) | 0x1073
        for index in range(361)
    ) + (0x13,),
}


def block_length(block):
    kind = block["kind"]
    if kind == "dense":
        return len(block["values"])
    if kind == "affine":
        return block["length"]
    if kind == "periodic":
        return block["repetitions"] * len(block["values"])
    raise ValueError(f"unknown setup block kind: {kind}")


def block_value(block, index):
    kind = block["kind"]
    if kind == "dense":
        return block["values"][index]
    if kind == "affine":
        return block["first"] + block["step"] * index
    values = block["values"]
    return values[index % len(values)] + block["stride"] * (index // len(values))


def checked_rows(artifact, active, label, expected_mask=None):
    circuit = artifact["circuit"]
    mask = circuit["decode_table_columns_mask"]
    if len(mask) != 9 or mask[:2] != [True, True]:
        raise ValueError(f"{label}: invalid native decoder mask")
    if expected_mask is not None and mask != expected_mask:
        raise ValueError(f"{label}: native decoder mask differs from imported Lean mask")
    width = sum(mask)
    tagged = bool(circuit["tables_ids_in_generic_lookups"])
    if len(artifact["columns"]) != width + int(tagged):
        raise ValueError(f"{label}: native decoder column count differs from mask")
    offset = circuit["offset_for_decoder_table"]
    count = artifact["program"]["text_words"]
    if circuit["total_tables_size"] - offset != count:
        raise ValueError(f"{label}: native decoder extent differs from public text")
    if any(index >= count or len(row) != width for index, row in active.items()):
        raise ValueError(f"{label}: Lean active row outside native decoder extent")
    sentinel = artifact["field_modulus"] - 1
    active_indices = sorted(active)
    for column_index, column in enumerate(artifact["columns"][:width]):
        position = 0
        compared = 0
        for block in column["blocks"]:
            length = block_length(block)
            start = max(position, offset)
            end = min(position + length, offset + count)
            if start < end:
                # Most padding is one affine sentinel block; verify it once.
                first_active = bisect.bisect_left(active_indices, start - offset)
                has_active = (first_active < len(active_indices) and
                              active_indices[first_active] < end - offset)
                if not has_active and block["kind"] == "affine" and block["step"] == 0:
                    if block["first"] != sentinel:
                        raise ValueError(f"{label}: non-sentinel padding at column {column_index}")
                else:
                    for row_position in range(start, end):
                        index = row_position - offset
                        expected = active[index][column_index] if index in active else sentinel
                        actual = block_value(block, row_position - position)
                        if actual != expected:
                            raise ValueError(
                                f"{label}: decoder row {index}, column {column_index}: "
                                f"Lean {expected}, Rust {actual}"
                            )
                compared += end - start
            position += length
        if position != artifact["trace_len"] or compared != count:
            raise ValueError(f"{label}: incomplete native column {column_index}")


def active_rows(path):
    result = {}
    with path.open(newline="") as source:
        for fields in csv.reader(source):
            if not fields:
                continue
            index, *values = map(int, fields)
            if index in result:
                raise ValueError(f"duplicate Lean row {index}")
            result[index] = values
    return result


def run_checked(command, label):
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode:
        detail = (result.stderr or result.stdout).strip()[-1200:]
        raise RuntimeError(f"{label} failed (exit {result.returncode}): {detail}")


def run_case(exporter, oracle, directory, text, image, config, family, cache):
    name = f"{text.stem}-{config}-{family}-{cache}"
    artifact_path = directory / f"{name}.json"
    lean_path = directory / f"{name}.csv"
    export = [str(exporter), family, str(image), str(text), str(artifact_path)]
    if config == "reduced":
        export.append("--reduced")
    if cache == "cached":
        export.append("--cached")
    run_checked(export, f"{name} native export")
    run_checked([str(oracle), config, family, str(text), str(lean_path)],
                f"{name} Lean oracle")
    artifact = json.loads(artifact_path.read_text())
    retained = pathlib.Path(__file__).resolve().parents[1] / "artifacts" / "setup" / f"{family}.json"
    expected_mask = json.loads(retained.read_text())["circuit"]["decode_table_columns_mask"]
    checked_rows(artifact, active_rows(lean_path), name, expected_mask)
    circuit_bytes = json.dumps(artifact["circuit"], sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(circuit_bytes).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", required=True, type=pathlib.Path)
    parser.add_argument("--oracle", required=True, type=pathlib.Path)
    parser.add_argument("--program", action="append", type=pathlib.Path,
                        help="public TEXT file; matching .bin supplies the initial image")
    parser.add_argument("--committed-verifiers", action="store_true",
                        help="check each committed FSV text under its production setup machine")
    parser.add_argument("--small-program", choices=tuple(SMALL_PROGRAMS),
                        help="check only one generated small public program")
    parser.add_argument("--work-dir", type=pathlib.Path)
    parser.add_argument("--configs", default="full,reduced,unified")
    parser.add_argument("--cache-modes", default="plain,cached")
    parser.add_argument("--families", default=",".join(FAMILIES))
    args = parser.parse_args()
    configs = args.configs.split(",")
    caches = args.cache_modes.split(",")
    families = args.families.split(",")
    if not set(configs) <= {"full", "reduced", "unified"} or not set(caches) <= {"plain", "cached"}:
        parser.error("unknown configuration or cache mode")
    if not set(families) <= set(FAMILIES):
        parser.error("unknown decoder family")
    if sum((bool(args.committed_verifiers), bool(args.program), bool(args.small_program))) > 1:
        parser.error("select only one program source")
    with tempfile.TemporaryDirectory(prefix="airbender-decoder-") if args.work_dir is None else _kept(args.work_dir) as work:
        directory = pathlib.Path(work)
        if args.committed_verifiers:
            repository = pathlib.Path(__file__).resolve().parents[3]
            texts = sorted((repository / "tools" / "gkr_verifier").glob("fsv_*.text"))
            if len(texts) != 5:
                raise ValueError(f"expected five committed verifier texts, found {len(texts)}")
            programs = [(text, text.with_suffix(".bin")) for text in texts]
        elif args.program:
            programs = [(text, text.with_suffix(".bin")) for text in args.program]
        else:
            programs = []
            cases = SMALL_PROGRAMS.items() if args.small_program is None else (
                (args.small_program, SMALL_PROGRAMS[args.small_program]),
            )
            for name, words in cases:
                path = directory / f"{name}.bin"
                path.write_bytes(b"".join(struct.pack("<I", word) for word in words))
                programs.append((path, path))
        hashes = {}
        for text, image in programs:
            if not text.is_file() or not image.is_file():
                raise FileNotFoundError(f"missing public text or image: {text}, {image}")
            for cache in caches:
                for config in configs:
                    if args.committed_verifiers and config != (
                        "reduced" if text.name.startswith("fsv_unrolled_") else "unified"
                    ):
                        continue
                    if text.stem == "split-keccak" and config != "full":
                        continue
                    for family in families:
                        if text.stem == "split-keccak" and family != "add-sub":
                            continue
                        if (config == "reduced" and family not in REDUCED_FAMILIES) or \
                           (config == "full" and family not in POOLED_FAMILIES) or \
                           (config == "unified" and family != "unified"):
                            continue
                        digest = run_case(args.exporter.resolve(), args.oracle.resolve(), directory,
                                          text.resolve(), image.resolve(), config, family, cache)
                        hashes[(text, cache, config, family)] = digest
                        print(f"PASS {text.name} {cache} {config} {family}", flush=True)
        for text, _ in programs:
            for cache in caches:
                for family in REDUCED_FAMILIES:
                    full = hashes.get((text, cache, "full", family))
                    reduced = hashes.get((text, cache, "reduced", family))
                    if full is not None and reduced is not None and full != reduced:
                        raise ValueError(f"{text.name} {cache} {family}: full/reduced circuit differs")
        for cache in caches:
            for config in configs:
                for family in families:
                    digests = [hashes.get((text, cache, config, family)) for text, _ in programs]
                    digests = [digest for digest in digests if digest is not None]
                    if len(set(digests)) > 1:
                        raise ValueError(f"{cache} {config} {family}: circuit depends on public text")
        print(f"PASS {len(hashes)} exact decoder row comparisons and circuit-object checks")


class _kept:
    def __init__(self, path):
        self.path = path

    def __enter__(self):
        self.path.mkdir(parents=True, exist_ok=True)
        return self.path

    def __exit__(self, *_):
        return False


if __name__ == "__main__":
    main()
