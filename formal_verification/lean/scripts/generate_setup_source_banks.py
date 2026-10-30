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
    nodes, memo = [], {}

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
        return memo[description]

    intern(None)
    root = intern(value)
    namespace = "Airbender.Setup.SourceCapture" + label
    module = "Airbender.Data.Setup.Source." + label
    proof_module = "Airbender.Proofs.FullUnsigned.Source." + label
    lines = [
        "import Lean.Compiler.NeverExtractAttr", "import Airbender.Import.SetupSourceBank", "",
        f"namespace {namespace}", "open Lean Airbender.Setup",
        "set_option maxRecDepth 16384", "set_option maxHeartbeats 2400000",
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
            body = ".array (" + indices(node[1]) + ")"
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
        f'def sourceSha256 : String := "{hashlib.sha256(raw).hexdigest()}"',
        f"end {namespace}", "",
    ]
    proof = [f"import {module}", "import Airbender.Proofs.FullUnsigned.SetupSourceCertificate", "",
             f"certify_source_bank {namespace}Proofs using {namespace}", ""]
    return {module: "\n".join(lines), proof_module: "\n".join(proof)}


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
