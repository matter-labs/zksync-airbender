#!/usr/bin/env python3
"""Untrusted source-to-native lookup-field identity synthesis.

Certificates contain native addresses, selectors and combinations of actual
copy equations. Neither side of an agreement is supplied by this generator.
The Lean importer must reconstruct both sides and kernel-check the identities.
This stage alone does not certify the lookup reduction graph or RAM lowering.
"""
import argparse
import json
from pathlib import Path
import re

from gkr_arithmetic_certificate import atom, coefficient, const, packed, plus, times

ROOT = Path(__file__).resolve().parents[3]


def table_ids():
    text = re.sub(r"//[^\n]*", "", (ROOT / "cs/src/definitions/table_type.rs").read_text())
    entries = text.split("pub enum TableType {", 1)[1].split("}", 1)[0]
    result, value = {}, 0
    for line in entries.splitlines():
        line = line.strip().rstrip(",")
        if not line:
            continue
        parts = line.split("=")
        if len(parts) == 2:
            value = int(parts[1].strip(), 0)
        result[parts[0].strip()] = value
        value += 1
    return result


def synthesis(pair, snapshot):
    if any(pair[field] != snapshot[field] for field in ("format_version", "family", "cached", "source")):
        raise ValueError("source sidecar is detached from the compilation")
    circuit, source = pair["circuit"], snapshot["semantic_inputs"]
    nsource = pair["source"]["num_variables"]
    addresses, ids = [], {}

    def address(value):
        # Witness-evaluation metadata uses the physical scratch-bank alias of
        # an intermediate GKR value. Interpret that storage alias through the
        # actual checked native bijection; it is not an independent variable
        # or an extra algebraic equation supplied by this certificate.
        if "ScratchSpace" in value:
            index = value["ScratchSpace"]
            target = circuit["scratch_space_mapping_rev"].get(str(index))
            forward = [wire for wire, slot in circuit["scratch_space_mapping"] if slot == index]
            if target is None or "InnerLayer" not in target or forward != [target]:
                raise ValueError("invalid native scratch storage alias")
            value = target
        encoded = json.dumps(value, sort_keys=True, separators=(",", ":"))
        if encoded not in ids:
            ids[encoded] = len(addresses)
            addresses.append(value)
        return ids[encoded]

    for index in range(nsource):
        if address(circuit["placement_data"][str(index)]) != index:
            raise ValueError("original source placements alias")

    def variable(index):
        if not isinstance(index, int) or not 0 <= index < nsource:
            raise ValueError("lookup references a non-source variable")
        return atom(index)

    def source_input(value):
        if "Variable" in value:
            return variable(value["Variable"])
        body = value["Expression"]
        result = const(coefficient(body["constant_coeff"]))
        for scalar, index in body["linear_terms"]:
            result = plus(result, variable(index), coefficient(scalar))
        return result

    tables = table_ids()

    def source_table(value):
        if "Constant" in value:
            return const(tables[value["Constant"]])
        if "Variable" in value:
            return variable(value["Variable"])
        return source_input(value["Expression"])

    def native_input(value):
        result = const(coefficient(value["constant"]))
        for scalar, wire in value["linear_terms"]:
            result = plus(result, atom(address(wire)), coefficient(scalar))
        return result

    copies, copy_equations = {}, []
    caches, decoder = {}, []
    for layer_index, layer in enumerate(circuit["layers"]):
        for wire, relation in layer["cached_relations"]:
            encoded = json.dumps(wire, sort_keys=True, separators=(",", ":"))
            if encoded in caches:
                raise ValueError("duplicate native cache address")
            caches[encoded] = relation
        for container_index, container in enumerate(("gates", "gates_with_external_connections")):
            for gate_index, gate in enumerate(layer[container]):
                kind, body = next(iter(gate["enforced_relation"].items()))
                if kind == "CopyInBaseField":
                    output, input_wire = address(body["output"]), address(body["input"])
                    if output in copies:
                        raise ValueError("duplicate copy producer")
                    copies[output] = (input_wire, len(copy_equations))
                    copy_equations.append(plus(atom(output), atom(input_wire), -1))
                if kind in ("LookupWithDensAndSetupExpressions", "LookupWithCachedDensAndSetup"):
                    decoder.append(([layer_index, container_index, gate_index], kind, body))

    def agreement(expected, actual):
        current, witness = plus(expected, actual, -1), {}
        while current:
            choice = next(((monomial, scalar, wire) for monomial, scalar in current.items()
                           for wire in monomial if wire in copies), None)
            if choice is None:
                raise ValueError(f"source lookup field has no identity modulo native copies: {packed(current)[:8]}")
            monomial, scalar, wire = choice
            visited, root = set(), wire
            while root in copies:
                if root in visited:
                    raise ValueError("cyclic native copy graph")
                visited.add(root)
                root = copies[root][0]
            _, equation = copies[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): scalar}
            current = plus(current, times(factor, copy_equations[equation]), -1)
            witness[equation] = plus(witness.get(equation, {}), factor)
        return [[packed(factor), equation] for equation, factor in sorted(witness.items()) if factor]

    eight = [query["input"] for query in source["range_checks"] if query["width"] == 8]
    sixteen = [query["input"] for query in source["range_checks"] if query["width"] == 16]
    if len(eight) + len(sixteen) != len(source["range_checks"]):
        raise ValueError("unsupported authored range-check width")
    generic = [{"row": eight[index:index + 2], "table": {"Constant": "RangeCheck8x8"}}
               for index in range(0, len(eight), 2)] + source["lookups"]
    executor = source["executor_machine_state"]
    decoder_row, decoder_mask = [], None
    if executor is not None:
        state = executor["decoder_data"]
        decoder_row = [variable(index) for index in executor["cycle_start_state"]["pc"] +
                       [state["rs1_index"], state["rs2_index"], state["rd_index"]] + state["imm"]]
        if state["funct3"] is not None:
            decoder_row.append(variable(state["funct3"]))
        if source["circuit_family_bitmask"]:
            mask = {}
            for index, wire in enumerate(source["circuit_family_bitmask"]):
                mask = plus(mask, variable(wire), 1 << index)
            decoder_row.append(mask)
        decoder_mask = variable(executor["execute"])
    widest = max((len(query["row"]) for query in generic), default=0)
    include_id = bool(decoder_row and widest)
    if executor is None and generic:
        include_id |= any(query["table"] != generic[0]["table"] for query in generic[1:])
    if not include_id and generic and ("Constant" not in generic[0]["table"] or
                                      any(query["table"] != generic[0]["table"] for query in generic)):
        raise ValueError("omitted table selector needs one fixed source table")
    width = max(len(decoder_row), widest) + int(include_id)
    if width != circuit["generic_lookup_tables_width"] or include_id != circuit["tables_ids_in_generic_lookups"]:
        raise ValueError("native lookup encoding geometry disagrees with source requests")
    if (len(generic) != len(circuit["generic_lookups"]) or
            len(sixteen) != len(circuit["range_check_16_lookup_expressions"]) or
            len(generic) + int(executor is not None) != circuit["num_generic_lookups"] or
            bool(executor is not None) != circuit["has_decoder_lookup"]):
        raise ValueError("native lookup request coverage disagrees with source")

    def encode(row, table):
        result = list(row) + [const(0)] * (width - int(include_id) - len(row))
        if include_id:
            result.append(table)
        if len(result) != width:
            raise ValueError("source lookup exceeds native encoding width")
        return result

    records = []
    for source_index, query in enumerate(generic):
        found = [(index, relation) for index, relation in enumerate(circuit["generic_lookups"])
                 if relation["lookup_set_index"] == source_index]
        if len(found) != 1:
            raise ValueError("missing or ambiguous generic lookup set index")
        native_index, native = found[0]
        expected = encode([source_input(value) for value in query["row"]], source_table(query["table"]))
        actual = [native_input(value) for value in native["columns"]]
        if len(actual) != len(expected):
            raise ValueError("native lookup columns changed")
        records.append({"kind": "generic", "source_index": source_index, "native_index": native_index,
                        "fields": [agreement(a, b) for a, b in zip(expected, actual)]})
    for source_index, value in enumerate(sixteen):
        found = [(index, relation) for index, relation in enumerate(circuit["range_check_16_lookup_expressions"])
                 if relation["lookup_set_index"] == source_index]
        if len(found) != 1:
            raise ValueError("missing or ambiguous scalar lookup set index")
        native_index, native = found[0]
        records.append({"kind": "range16", "source_index": source_index, "native_index": native_index,
                        "fields": [agreement(source_input(value), native_input(native["input"]))]})
    decoder_gate = None
    if executor is not None:
        if len(decoder) != 1:
            raise ValueError("decoder lookup must have exactly one actual graph leaf")
        decoder_gate, kind, body = decoder[0]
        mask, value = body["input"]
        if kind == "LookupWithCachedDensAndSetup":
            relation = caches[json.dumps(value, sort_keys=True, separators=(",", ":"))]
            value = relation["VectorizedLookup"]
        expected = [decoder_mask] + encode(decoder_row, const(tables["Decoder"]))
        actual = [atom(address(mask))] + [native_input(column) for column in value["columns"]]
        if len(actual) != len(expected):
            raise ValueError("native decoder columns changed")
        records.append({"kind": "decoder", "source_index": 0, "native_index": 0,
                        "fields": [agreement(a, b) for a, b in zip(expected, actual)]})
    elif decoder:
        raise ValueError("unexpected masked decoder lookup in delegation graph")
    return {"format_version": 1, "addresses": addresses, "decoder_gate": decoder_gate, "rows": records,
            "counts": {"source_variables": nsource, "lower_variables": len(addresses),
                       "copy_equations": len(copy_equations), "generic_requests": len(generic),
                       "range16_requests": len(sixteen), "decoder_requests": int(executor is not None),
                       "agreements": sum(len(record["fields"]) for record in records)}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair", type=Path)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = synthesis(json.loads(args.pair.read_text()), json.loads(args.source.read_text()))
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps(result["counts"], sort_keys=True))
