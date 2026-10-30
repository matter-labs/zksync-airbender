#!/usr/bin/env python3
"""Retain exact setup source bytes in shared syntax data.

The generator emits data and ordinary kernel proof terms. It does not
prove that the retained physical rows match the canonical table definitions.
Tests.SetupSourceCaptures compares the interpreted source with each raw file.
"""

import argparse
import hashlib
import json
from pathlib import Path

LEAN = Path(__file__).resolve().parents[1]
FAMILIES = {
    "Parity": "keccak-column-parity",
    "Theta": "keccak-theta-rho",
    "Chi": "keccak-chi5",
}
HEADS = dict(zip("-0123456789", ["minus", "zero", "one", "two", "three", "four",
                                "five", "six", "seven", "eight", "nine"]))


def sequence(items):
    if not items:
        return "[]"
    chunks = ["[" + ", ".join(items[i:i + 64]) + "]" for i in range(0, len(items), 64)]

    def join(parts):
        if len(parts) == 1:
            return parts[0]
        mid = len(parts) // 2
        return "(" + join(parts[:mid]) + " ++ " + join(parts[mid:]) + ")"

    return join(chunks)


def indices(values):
    if len(values) <= 1024:
        return sequence([str(value) for value in values])
    bits = max(1, max(values, default=0).bit_length())
    output = bytearray()
    carry = available = 0
    for value in values:
        carry |= value << available
        available += bits
        while available >= 8:
            output.append(carry & 255)
            carry >>= 8
            available -= 8
    if available:
        output.append(carry)
    return f"decodeIndices {1 << bits} {len(values)} {hex(int.from_bytes(output, 'little'))}"


def choice(items):
    def tree(lo, hi):
        if hi - lo == 1:
            return items[lo]
        mid = (lo + hi) // 2
        return f"(if index < {mid} then {tree(lo, mid)} else {tree(mid, hi)})"

    assert items
    return tree(0, len(items))


def generate(label, filename):
    path = LEAN / "artifacts/setup" / (filename + ".json")
    raw = path.read_bytes()
    value = json.loads(raw)
    if json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode() != raw:
        raise ValueError(f"Source is not in the retained exact spelling: {path}")
    texts, numbers = {""}, {0}

    def collect(entry):
        if isinstance(entry, dict):
            for key, child in entry.items():
                texts.add(key)
                collect(child)
        elif isinstance(entry, list):
            for child in entry:
                collect(child)
        elif isinstance(entry, str):
            texts.add(entry)
        elif type(entry) is int:
            numbers.add(entry)
        elif entry is not None and type(entry) is not bool:
            raise ValueError(f"Unsupported setup source value: {entry!r}")

    collect(value)
    if any(ord(c) < 32 or c in '\\"' for text in texts for c in text):
        raise ValueError(f"Source needs escaped string support: {path}")
    texts, numbers = sorted(texts), sorted(numbers)
    text_index = {text: i for i, text in enumerate(texts)}
    number_index = {number: i for i, number in enumerate(numbers)}
    nodes, memo, node_values = [], {}, []

    def intern(entry):
        if entry is None:
            description = ("null",)
        elif type(entry) is bool:
            description = ("boolean", entry)
        elif type(entry) is int:
            description = ("number", number_index[entry])
        elif isinstance(entry, str):
            description = ("string", text_index[entry])
        elif isinstance(entry, list):
            description = ("array", tuple(intern(child) for child in entry))
        else:
            description = ("object", tuple((text_index[key], intern(child))
                                           for key, child in entry.items()))
        if description not in memo:
            memo[description] = len(nodes)
            nodes.append(description)
            node_values.append(entry)
        return memo[description]

    intern(None)
    root = intern(value)
    column_ids = [intern(column) for column in value["columns"]]
    block_arrays = {}
    for column in value["columns"]:
        if list(column) != ["blocks"]:
            raise ValueError("Unexpected retained column fields")
        array_id = intern(column["blocks"])
        block_arrays[array_id] = sorted(set(nodes[array_id][1]))
    columns_id = intern(value["columns"])
    indexed_arrays = dict(block_arrays)
    indexed_arrays[columns_id] = sorted(set(column_ids))
    block_ids = sorted({index for pool in block_arrays.values() for index in pool})
    large_arrays = sorted({intern(node_values[index]["values"]) for index in block_ids
                           if len(node_values[index].get("values", [])) > 64})
    for array_id in large_arrays:
        indexed_arrays[array_id] = sorted(set(nodes[array_id][1]))
    natural_ids = sorted({child for array_id in large_arrays for child in indexed_arrays[array_id]})
    for index in natural_ids:
        if type(node_values[index]) is not int or node_values[index] < 0:
            raise ValueError("Retained RLE payload is not a natural number")
    namespace = "Airbender.Setup.SourceCapture" + label
    module = "Airbender.Data.Setup.Source." + label
    proof_module = "Airbender.Proofs.FullUnsigned.Source." + label
    lines = [
        "import Lean.Compiler.NeverExtractAttr", "import Airbender.Import.SetupSourceBank", "",
        f"namespace {namespace}", "open Lean Airbender.Setup",
        "set_option maxRecDepth 16384", "set_option maxHeartbeats 2400000", "set_option Elab.async false",
        "set_option compiler.extract_closed false", "",
        "/-- Decode packed index data. Keep recursion in tail position. -/",
        "private def decodeIndices (base count packed : Nat) : List Nat :=",
        "  let rec go : Nat → Nat → List Nat → List Nat",
        "    | 0, _, earlier => earlier.reverse",
        "    | remaining + 1, value, earlier =>",
        "      go remaining (value / base) ((value % base) :: earlier)",
        "  go count packed []", "",
    ]
    for i, text in enumerate(texts):
        lines.append(f"private def text_{i} : String := " + json.dumps(text, ensure_ascii=False))
    for i, number in enumerate(numbers):
        spelling = str(number)
        tail = "[" + ", ".join("'" + c + "'" for c in spelling[1:]) + "]"
        lines.append(f"private def token_{i} : SourceData.NumberToken := "
                     f"⟨.{HEADS[spelling[0]]}, {tail}, ⟨({number}), 0⟩⟩")
    lines += ["def text (index : Nat) : String := " + choice([f"text_{i}" for i in range(len(texts))]),
              "def token (index : Nat) : SourceData.NumberToken := " +
              choice([f"token_{i}" for i in range(len(numbers))])]
    for array_id, children in indexed_arrays.items():
        positions = {child: index for index, child in enumerate(children)}
        lines.append(f"def select_{array_id} (index : Nat) : Nat := " +
                     choice([str(child) for child in children]))
        lines.append(f"def entries_{array_id} : List Nat := " +
                     indices([positions[child] for child in nodes[array_id][1]]))

    source_lines = lines
    lines = [f"import {module}", "import Airbender.Import.SetupSourceBindings", "",
             f"namespace {namespace}", "open Lean Airbender.Setup",
             "set_option maxRecDepth 16384", "set_option maxHeartbeats 2400000", "set_option Elab.async false",
             "set_option compiler.extract_closed false", ""]
    def native_block(block):
        kind = block["kind"]
        if kind == "affine":
            return f'.affine {block["length"]} {block["first"]} ({block["step"]})'
        array_id = intern(block["values"])
        values = (f"payload_{array_id}" if array_id in large_arrays else
                  "#[" + ", ".join(map(str, block["values"])) + "]")
        if kind == "dense":
            return ".dense " + values
        if kind == "periodic":
            return f'.periodic {block["repetitions"]} ({block["stride"]}) {values}'
        raise ValueError("Unexpected retained block kind")

    for array_id in large_arrays:
        children = indexed_arrays[array_id]
        argument = "_index" if len(children) == 1 else "index"
        lines.append(f"private def naturals_{array_id} ({argument} : Nat) : Nat := " +
                     choice([str(node_values[child]) for child in children]))
        lines.append(f"private noncomputable def valuesBinding_{array_id} : SourceBank.ValueArrayBinding := " +
                     f"⟨{array_id}, select_{array_id}, naturals_{array_id}, entries_{array_id}⟩")
        lines.append(f"private noncomputable def payload_{array_id} : Array Nat := valuesBinding_{array_id}.values")
    lines.append("def naturalSources : List (Nat × Nat) := " +
                 sequence([f"({index}, {node_values[index]})" for index in natural_ids]))
    lines.append("noncomputable def valueArrays : List (SourceBank.ValueArrayBinding × Array Nat) := " +
                 sequence([f"(valuesBinding_{index}, payload_{index})" for index in large_arrays]))
    lines.append("def blockArrays : List (Nat × Nat) := " +
                 sequence([f'({index}, {intern(node_values[index]["values"])})' for index in block_ids
                           if "values" in node_values[index] and intern(node_values[index]["values"]) in large_arrays]))
    for index in block_ids:
        lines.append(f"@[noinline, never_extract] private noncomputable def block_{index} (salt : Nat) : Block := " +
                     "if salt = 0 then " + native_block(node_values[index]) + " else .affine 0 0 0")
    for array_id, children in block_arrays.items():
        lines.append(f"private noncomputable def blocks_{array_id} (index : Nat) : Block := " +
                     choice([f"(block_{child} 0)" for child in children]))
    for index in sorted(set(column_ids)):
        key_index, array_id = nodes[index][1][0]
        lines.append(f"private noncomputable def binding_{index} : SourceBank.ColumnBinding := " +
                     f"⟨{index}, {key_index}, {array_id}, select_{array_id}, blocks_{array_id}, entries_{array_id}⟩")
        lines.append(f"private noncomputable def column_{index} : Column := binding_{index}.column")
    lines.append("noncomputable def blockSources : List (Nat × Block) := " +
                 sequence([f"({index}, (block_{index} 0))" for index in block_ids]))
    lines.append("noncomputable def columnBindings : List (SourceBank.ColumnBinding × Column) := " +
                 sequence([f"(binding_{index}, column_{index})" for index in sorted(set(column_ids))]))
    lines.append("noncomputable def column (index : Nat) : Column := " +
                 choice([f"column_{index}" for index in indexed_arrays[columns_id]]))
    lines.append(f"def columnsIndex : Nat := {columns_id}")
    lines.append(f"def columnsChildren : Nat → Nat := select_{columns_id}")
    lines.append(f"def columnsEntries : List Nat := entries_{columns_id}")
    lines.append("noncomputable def columns : Array Column := (columnsEntries.map column).toArray")
    lines += [f"end {namespace}", ""]
    rle_text = "\n".join(lines)
    lines = source_lines
    descriptions, levels = [], []
    for node in nodes:
        kind = node[0]
        depth = 1
        if kind == "null":
            body = ".null"
        elif kind == "boolean":
            body = ".boolean " + str(node[1]).lower()
        elif kind in ("number", "string"):
            body = f".{kind} {node[1]}"
        elif kind == "array":
            body = (f".indexedArray select_{len(descriptions)} entries_{len(descriptions)}"
                    if len(descriptions) in indexed_arrays else ".array (" + indices(node[1]) + ")")
            depth += max((levels[child] for child in node[1]), default=0)
        else:
            body = ".object " + sequence([f"({key}, {child})" for key, child in node[1]])
            depth += max((levels[child] for _, child in node[1]), default=0)
        descriptions.append(body)
        levels.append(depth)

    def bank(lo, hi):
        if hi - lo == 1:
            return f"(.leaf ({descriptions[lo]}))"
        mid = (lo + hi) // 2
        left, right = bank(lo, mid), bank(mid, hi)
        body = f"(.branch {mid} {left} {right})"
        if hi - lo <= 64:
            return body
        name = f"bank_{lo}_{hi}"
        lines.append(f"@[noinline, never_extract] private def {name} (salt : Nat) : SourceBank.Bank := "
                     f"if salt = 0 then {body} else .leaf .null")
        return f"({name} 0)"

    root_bank = bank(0, len(nodes))
    lines += [
        "def strings : List String := " + sequence([f"text_{i}" for i in range(len(texts))]),
        "def tokens : List SourceData.NumberToken := " + sequence([f"token_{i}" for i in range(len(numbers))]),
        "def bank : SourceBank.Bank := " + root_bank,
        f"def fuel : Nat := {levels[root] - 1}", f"def rootIndex : Nat := {root}",
        "def rootEntries : List (Nat × Nat) := " + sequence([f"({key}, {child})" for key, child in nodes[root][1]]),
        "def root : SourceData.Node := SourceBank.evaluate text token bank (fuel + 1) rootIndex",
        "def source : String := String.ofList root.bytes",
        f"def byteLength : Nat := {len(raw)}",
        f'def traceLength : Nat := {value["trace_len"]}',
        f'def sourceSha256 : String := "{hashlib.sha256(raw).hexdigest()}"',
        f"end {namespace}", "",
    ]
    proof = [f"import {module}RLE", "import Airbender.Proofs.FullUnsigned.SetupSourceCertificate", "",
             "set_option Elab.async false",
             f"certify_source_bank {namespace}Proofs using {namespace}",
             f"certify_source_rle {namespace}Proofs using {namespace}", ""]
    return {module: "\n".join(lines), module + "RLE": rle_text, proof_module: "\n".join(proof)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--family", choices=FAMILIES)
    args = parser.parse_args()
    count = 0
    for label, filename in FAMILIES.items():
        if args.family and args.family != label:
            continue
        for module, text in generate(label, filename).items():
            path = LEAN / (module.replace(".", "/") + ".lean")
            if args.check:
                if not path.is_file() or path.read_text() != text:
                    raise SystemExit(f"Stale setup source data: {path.relative_to(LEAN)}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            count += 1
    print(f"PASS setup source generation {'check' if args.check else 'write'}: {count} modules")


if __name__ == "__main__":
    main()
