#!/usr/bin/env python3
"""Generate worker query selectors. Lean checks coverage, expansion and native groups."""
import argparse
import json
from pathlib import Path
from check_compiler_captures import FAMILIES, cached_layout

ROOT = Path(__file__).resolve().parents[1]
GROUPS = {"GenericLookup": 0, "Lookup16Bits": 1, "LookupTimestamps": 2}
WORKERS = {"Bigint": "bigint", "BlakeG": "blake-g", "BlakeRound": "blake-round",
           "KeccakColumnParity": "keccak-column-parity", "KeccakThetaRho": "keccak-theta-rho",
           "KeccakChi5": "keccak-chi5"}

def address_key(address):
    return json.dumps(address, sort_keys=True, separators=(",", ":"))


def native_chains(circuit):
    """Every primitive query in gate and operand order, and the (gate, operand) position and group of every operand
    of each public lookup chain, in output and chain order."""
    gates = [gate["enforced_relation"] for layer in circuit["layers"]
             for gate in layer["gates"] + layer["gates_with_external_connections"]]
    definitions, producers = [], {}

    def definition(output, kind, data):
        key = address_key(output)
        if key in producers:
            raise ValueError("duplicate actual affine definition")
        producers[key] = len(definitions)
        definitions.append((output, kind, data))

    for layer in circuit["layers"]:
        for output, relation in layer["cached_relations"]:
            kind, data = next(iter(relation.items()))
            if kind == "SingleColumnLookup":
                definition(output, "scalar", data["relation"])
            elif kind == "VectorizedLookup":
                definition(output, "vector", data)
            elif kind == "VectorizedLookupSetup":
                definition(output, "setup_vector", data)
            elif kind == "MemoryTuple":
                definition(output, "memory", data)
            else:
                raise ValueError("unknown cache kind")
    for relation in gates:
        kind, data = next(iter(relation.items()))
        if kind in ("CopyInBaseField", "CopyInExtensionField"):
            definition(data["output"], "copy", data["input"])
        elif kind == "MaterializeSingleLookupInput":
            definition(data["output"], "scalar", data["input"])
        elif kind == "MaterializedVectorLookupInput":
            definition(data["output"], "vector", data["input"])

    def resolve(kind, data):
        selected, seen = [], set()
        while kind == "address" and address_key(data) in producers:
            index = producers[address_key(data)]
            if index in seen:
                raise ValueError("cyclic operand expansion")
            seen.add(index)
            selected.append(index)
            _, kind, data = definitions[index]
            if kind == "copy":
                kind = "address"
        if kind == "address":
            return {"kind": "scalar", "columns": [{"cell": data}]}, selected, None
        if kind == "scalar":
            return {"kind": "scalar", "columns": [{"linear": data["input"]}]}, selected, data["lookup_set_index"]
        if kind == "vector":
            return {"kind": "vector", "columns": [{"linear": row} for row in data["columns"]]}, selected, data["lookup_set_index"]
        if kind == "setup_vector":
            return {"kind": "vector", "columns": [{"cell": address} for address in data]}, selected, None
        raise ValueError("lookup operand is not a supported base-column encoding")

    registry, meanings = [], {}
    gate_index, operand_index = 0, 0

    def leaf(kind, data, weight="one", mask=None):
        nonlocal operand_index
        encoding, expansion, request = resolve(kind, data)
        index = len(registry)
        registry.append({"encoding": encoding, "expansion": expansion, "request": request,
                         "weight": weight, "mask": mask})
        registry[-1]["locator"] = [gate_index, operand_index]
        operand_index += 1
        return index

    def read_pair(pair):
        numerator, denominator = (meanings.get(address_key(address)) for address in pair)
        if numerator is None or denominator is None or numerator[1] or not denominator[1] or numerator[0] != denominator[0]:
            raise ValueError("actual native pair components disagree")
        return list(numerator[0])

    def write_pair(pair, leaves):
        meanings[address_key(pair[0])] = (leaves, False)
        meanings[address_key(pair[1])] = (leaves, True)

    for gate_index, relation in enumerate(gates):
        operand_index = 0
        kind, data = next(iter(relation.items()))
        if kind == "CopyInExtensionField":
            if address_key(data["input"]) in meanings:
                meanings[address_key(data["output"])] = meanings[address_key(data["input"])]
        elif kind == "AggregateLookupRationalPair":
            write_pair(data["output"], read_pair(data["input"][0]) + read_pair(data["input"][1]))
        elif kind in ("LookupPairFromBaseInputs", "LookupPairFromVectorInputs"):
            tag = "scalar" if kind == "LookupPairFromBaseInputs" else "vector"
            write_pair(data["output"], [leaf(tag, value) for value in data["input"]])
        elif kind in ("LookupPairFromMaterializedBaseInputs", "LookupPairFromMaterializedVectorInputs"):
            write_pair(data["output"], [leaf("address", value) for value in data["input"]])
        elif kind in ("LookupFromBaseInputsWithSetup", "LookupFromVectorInputWithSetup",
                      "LookupFromMaterializedBaseInputWithSetup", "LookupFromMaterializedVectorInputWithSetup",
                      "LookupWithCachedDensAndSetup", "LookupWithDensAndSetupExpressions"):
            if kind == "LookupFromBaseInputsWithSetup":
                query, table = ("scalar", data["input"]), ("address", data["setup"][1])
                weight, mask = "one", None
            elif kind == "LookupFromVectorInputWithSetup":
                query, table = ("vector", data["input"]), ("setup_vector", data["setup"][1])
                weight, mask = "one", None
            elif kind == "LookupWithCachedDensAndSetup":
                query, table = ("address", data["input"][1]), ("address", data["setup"][1])
                weight, mask = "mask", data["input"][0]
            elif kind == "LookupWithDensAndSetupExpressions":
                query, table = ("vector", data["input"][1]), ("setup_vector", data["setup"][1])
                weight, mask = "mask", data["input"][0]
            else:
                query, table = ("address", data["input"]), ("address", data["setup"][1])
                weight, mask = "one", None
            write_pair(data["output"], [leaf(*query, weight, mask), leaf(*table, "setup", data["setup"][0])])
        elif kind in ("LookupUnbalancedPairWithMaterializedBaseInputs", "LookupUnbalancedPairWithMaterializedVectorInputs",
                      "LookupUnbalancedPairWithVectorInputs"):
            tag = "vector" if kind == "LookupUnbalancedPairWithVectorInputs" else "address"
            write_pair(data["output"], read_pair(data["input"]) + [leaf(tag, data["remainder"])])
        elif kind.startswith("Lookup"):
            raise ValueError("unhandled native lookup consumer: " + kind)

    selected, chains = [], []
    for kind, output in circuit["global_output_map"].items():
        if kind not in GROUPS:
            continue
        leaves = read_pair(output)
        if len(leaves) != len(set(leaves)):
            raise ValueError("A native query occurs twice in one chain")
        for index in leaves:
            entry = dict(registry[index])
            entry["group"] = GROUPS[kind]
            chains.append((tuple(entry["locator"]), GROUPS[kind]))
            if entry["weight"] != "setup":
                selected.append(entry)
    return sorted(selected, key=lambda entry: entry["locator"]), chains


def selectors(circuit):
    return native_chains(circuit)[0]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    for name, family in WORKERS.items():
        path = cached_layout(FAMILIES[family])
        entries = selectors(json.loads(path.read_text()))
        terms = [f'⟨{row["group"]}, {row["locator"][0]}, {row["locator"][1]}, {row["expansion"]}⟩'
                 for row in entries]
        content = (f"module\npublic import Human.Compiler.NativeLookups\n"
                   f"public import Human.Compiler.Captures.{name}\n\n@[expose] public section\n"
                   "namespace Airbender.Compiler.NativeWorkerLookups\n\n"
                   "/-- Every primitive query of the cached worker, in gate and operand order. -/\n"
                   f"def {name[0].lower() + name[1:]}Selectors : List NativeLookups.Selector := [\n  "
                   + ",\n  ".join(terms) + "\n]\n\nend Airbender.Compiler.NativeWorkerLookups\n")
        destination = ROOT / "human/Human/Compiler/LookupSelectors/Workers" / (name + ".lean")
        if args.check:
            if not destination.exists() or destination.read_text() != content:
                raise SystemExit("Worker selectors differ: " + name)
        else:
            destination.parent.mkdir(exist_ok=True)
            destination.write_text(content)
        print(name, len(entries), "checked query positions")


if __name__ == "__main__":
    main()
