#!/usr/bin/env python3
"""Untrusted selectors/witnesses from actual lookup operands to authored fields.

This generator never supplies replacement source or target equations. Native
operand encodings must be reconstructed from selected actual definitions by
the Lean importer, then checked against the actual registry payload.
"""
import argparse
import json

from export_gkr_translations import FAMILIES, LEAN
from gkr_arithmetic_certificate import PRIME, atom, coefficient, const, packed, plus, times
from gkr_wiring_instances import CASES


def address_key(address):
    return json.dumps(address, sort_keys=True, separators=(",", ":"))


def synthesis(pair, previous):
    circuit = pair["circuit"]
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

    address_ids = {address_key(address): index for index, address in enumerate(previous["addresses"])}

    def address_index(address):
        if "ScratchSpace" in address:
            address = circuit["scratch_space_mapping_rev"][str(address["ScratchSpace"])]
        key = address_key(address)
        # Timestamp metadata also uses compiler-generated auxiliary inputs.
        # Temporary symbols suffice to select those metadata rows; original
        # source-field witnesses below must stay inside the retained bank.
        if key not in address_ids:
            address_ids[key] = len(address_ids)
        return address_ids[key]

    def column_polynomial(column):
        if "cell" in column:
            return atom(address_index(column["cell"]))
        row = column["linear"]
        result = const(coefficient(row["constant"]))
        for scalar, address in row["linear_terms"]:
            result = plus(result, atom(address_index(address)), coefficient(scalar))
        return result

    copies, equations = {}, []
    for relation in gates:
        if "CopyInBaseField" in relation:
            row = relation["CopyInBaseField"]
            output, source = address_index(row["output"]), address_index(row["input"])
            copies[output] = source, len(equations)
            equations.append(plus(atom(output), atom(source), -1))

    def reduce_copy(poly):
        poly, witness = dict(poly), {}
        while True:
            choice = next(((monomial, scalar, wire) for monomial, scalar in poly.items()
                           for wire in monomial if wire in copies), None)
            if choice is None:
                return poly, witness
            monomial, scalar, wire = choice
            _, index = copies[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): scalar}
            poly = plus(poly, times(factor, equations[index]), -1)
            witness[index] = plus(witness.get(index, {}), factor)

    def decode_poly(encoded):
        return {tuple(monomial): scalar for scalar, monomial in encoded}

    def identity(metadata, actual, prior):
        expected = metadata
        for multiplier, index in prior:
            expected = plus(expected, times(decode_poly(multiplier), equations[index]))
        if any(wire >= len(previous["addresses"]) for poly in (expected, actual) for monomial in poly for wire in monomial):
            raise ValueError("authored field requires a wire outside its independently retained bank")
        remainder, witness = reduce_copy(plus(expected, actual, -1))
        if remainder:
            raise ValueError("actual operand is not the authored source field modulo copies")
        return [[packed(value), index] for index, value in sorted(witness.items()) if value]

    source_rows = {(row["kind"], row["native_index"]): (index, row)
                   for index, row in enumerate(previous["rows"])}
    operands, groups = [], {}
    for group, output in circuit["global_output_map"].items():
        if group not in ("GenericLookup", "Lookup16Bits", "LookupTimestamps"):
            continue
        leaves = read_pair(output)
        if len(leaves) != len(set(leaves)):
            raise ValueError("shared rational leaf requires occurrence-based source correspondence")
        bank = {"GenericLookup": circuit["generic_lookups"], "Lookup16Bits": circuit["range_check_16_lookup_expressions"],
                "LookupTimestamps": circuit["timestamp_range_check_lookup_expressions"]}[group]
        normalized_bank = []
        for row in bank:
            columns = row["columns"] if group == "GenericLookup" else [row["input"]]
            normalized_bank.append([reduce_copy(column_polynomial({"linear": column}))[0] for column in columns])
        used, labels = set(), []
        for index in leaves:
            value = registry[index]
            columns = value["encoding"]["columns"]
            record = {"native_leaf": index, "locator": value["locator"],
                      "expansion": value["expansion"], "group": group,
                      "source_row": None, "fields": []}
            if value["weight"] == "setup":
                labels.append(len(bank) + int(group == "GenericLookup" and circuit["has_decoder_lookup"]))
                record["kind"] = "setup"
            elif value["weight"] == "mask":
                if group != "GenericLookup":
                    raise ValueError("decoder mask outside generic root")
                row_index, row = source_rows["decoder", 0]
                expected = [{"cell": value["mask"]}] + columns
                record.update(kind="decoder", source_row=row_index, fields=[
                    identity(column_polynomial(column), column_polynomial(column), prior)
                    for column, prior in zip(expected, row["fields"], strict=True)])
                labels.append(len(bank))
            else:
                actual = [column_polynomial(column) for column in columns]
                canonical = [reduce_copy(poly)[0] for poly in actual]
                candidates = [i for i, row in enumerate(normalized_bank) if row == canonical and i not in used]
                selected = value["request"] if value["request"] is not None else (candidates[0] if candidates else None)
                if selected not in candidates:
                    raise ValueError("consumed query does not match an unused source request")
                used.add(selected)
                labels.append(selected)
                record.update(kind="timestamp" if group == "LookupTimestamps" else "query", source_index=selected)
                if group != "LookupTimestamps":
                    row_index, row = source_rows["generic" if group == "GenericLookup" else "range16", selected]
                    metadata_row = bank[selected]
                    metadata = metadata_row["columns"] if group == "GenericLookup" else [metadata_row["input"]]
                    record.update(source_row=row_index, fields=[identity(column_polynomial({"linear": column}), poly, prior)
                                  for column, poly, prior in zip(metadata, actual, row["fields"], strict=True)])
            operands.append(record)
        expected_size = len(bank) + 1 + int(group == "GenericLookup" and circuit["has_decoder_lookup"])
        if sorted(labels) != list(range(expected_size)) or len(used) != len(bank):
            raise ValueError("source query multiset is incomplete")
        groups[group] = {"native_leaves": leaves, "source_labels": labels}
    fields = sum(len(row.get("fields", [])) for row in operands)
    return {"format_version": 1, "operands": sorted(operands, key=lambda row: row["native_leaf"]), "groups": groups,
            "counts": {"definitions": len(definitions), "registry": len(registry), "source_fields": fields,
                       "nonempty_witnesses": sum(bool(witness) for row in operands for witness in row.get("fields", []))}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", action="append", choices=FAMILIES)
    parser.add_argument("--write", action="store_true", help="write checked-selector Lean instance modules")
    parser.add_argument("--check", action="store_true", help="check retained selector modules without changing files")
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ("uncached", "cached"):
            name = family + "-" + mode
            root = LEAN / "artifacts/compiler"
            certificate = synthesis(json.loads((root / (name + ".json")).read_text()),
                                    json.loads((root / "lookup" / (name + ".json")).read_text()))
            if args.write or args.check:
                case = stem + mode.title()
                selectors = json.dumps(json.dumps(certificate, separators=(",", ":")))
                size = len(certificate["operands"])
                native_imports = ["GKRProtocol.LookupSourceImport", f"GKRProtocol.Native.{case}",
                                  f"GKRProtocol.LookupNative.{case}"]
                modules = [(case, native_imports, 3, 0, size)]
                if family == "blake-round":
                    foundation = case + "Foundation"
                    parts = [(case + f"Part{index}", [f"GKRProtocol.LookupSourceNative.{foundation}"],
                              1, start, min(start + 32, size)) for index, start in enumerate(range(0, size, 32))]
                    modules = [(foundation, native_imports, 0, 0, 0)] + parts + [
                        (case, [f"GKRProtocol.LookupSourceNative.{part[0]}" for part in parts], 2, 0, 0)]
                for module, imports, phase, start, stop in modules:
                    destination = LEAN / "GKRProtocol/LookupSourceNative" / (module + ".lean")
                    content = ("".join(f"import {dependency}\n" for dependency in imports) + "\n" +
                        f"namespace Airbender.Compiler.LookupSourceNative.{case}\n"
                        "open Airbender Airbender.Compiler\n"
                        "set_option warningAsError true\n"
                        "set_option Elab.async false\n"
                        "set_option maxRecDepth 32768\n"
                        "set_option maxHeartbeats 4000000\n\n"
                        f'import_source_lookups native from "artifacts/compiler/{name}.json"\n'
                        f'  certificate "artifacts/compiler/lookup/{name}.json"\n'
                        f"  selectors {selectors}\n"
                        f"  reference Airbender.Compiler.LookupNative.{case}.native\n"
                        f"  typing Airbender.Compiler.ConsumerNative.{case}.native.typing\n"
                        f"  phase {phase} start {start} stop {stop}\n\n"
                        f"end Airbender.Compiler.LookupSourceNative.{case}\n")
                    if args.check and (not destination.exists() or destination.read_text() != content):
                        raise ValueError(f"source operand selectors changed: {module}")
                    if args.write and (not destination.exists() or destination.read_text() != content):
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        destination.write_text(content)
            print(name, json.dumps(certificate["counts"], sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
