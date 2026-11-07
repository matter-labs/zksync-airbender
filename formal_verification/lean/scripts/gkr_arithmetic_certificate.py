#!/usr/bin/env python3
"""Untrusted certificate synthesis for the original native arithmetic slice.

The Lean importer reads source expressions and native gates independently.
This file emits only wire/selection data and polynomial-identity witnesses.
It never supplies the source or lowered equations being certified.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path

PRIME = 2013265921
MONTGOMERY_INVERSE = 943718400


def cleaned(poly):
    return {key: value % PRIME for key, value in poly.items() if value % PRIME}


def plus(left, right, scale=1):
    result = dict(left)
    for key, value in right.items():
        result[key] = (result.get(key, 0) + scale * value) % PRIME
    return cleaned(result)


def times(left, right):
    result = defaultdict(int)
    for a, x in left.items():
        for b, y in right.items():
            result[tuple(sorted(a + b))] += x * y
    return cleaned(result)


def const(value):
    return cleaned({(): value})


def atom(index):
    return {(index,): 1}


def coefficient(raw):
    if not isinstance(raw, int) or not 0 <= raw < PRIME:
        raise ValueError("invalid native BabyBear Montgomery coefficient")
    return raw * MONTGOMERY_INVERSE % PRIME


def expression(tree, variable):
    if len(tree) != 1:
        raise ValueError("invalid native expression")
    kind, value = next(iter(tree.items()))
    if kind == "Constant":
        return const(coefficient(value))
    if kind in ("Var", "Place"):
        return atom(variable(value))
    if kind == "Sum":
        result = {}
        for term in value:
            result = plus(result, expression(term, variable))
        return result
    if kind == "Product":
        result = const(1)
        for term in value:
            result = times(result, expression(term, variable))
        return result
    raise ValueError("unsupported expression constructor: " + kind)


def key(poly):
    return tuple(sorted(cleaned(poly).items()))


def packed(poly):
    return [[value, list(monomial)] for monomial, value in sorted(cleaned(poly).items())]


def synthesis(pair):
    source, circuit = pair["source"], pair["circuit"]
    count = source["num_variables"]
    if pair["format_version"] != 1 or count <= 0:
        raise ValueError("unsupported or empty source snapshot")
    addresses, address_ids = [], {}

    def address(value):
        encoded = json.dumps(value, sort_keys=True, separators=(",", ":"))
        if encoded not in address_ids:
            address_ids[encoded] = len(addresses)
            addresses.append(value)
        return address_ids[encoded]

    placement = []
    for index in range(count):
        if str(index) not in circuit["placement_data"]:
            raise ValueError(f"original source variable {index} has no placement")
        placement.append(address(circuit["placement_data"][str(index)]))
    if placement != list(range(count)):
        raise ValueError("original source placements alias")

    def source_variable(value):
        if not isinstance(value, int) or not 0 <= value < count:
            raise ValueError("source variable outside original CircuitOutput")
        return value

    sources = []
    for statement in source["statements"]:
        kind, body = next(iter(statement.items()))
        poly = expression(body["expr"], source_variable)
        if kind == "Define":
            poly = plus(atom(source_variable(body["dst"])), poly, -1)
        elif kind != "AssertZero":
            raise ValueError("unsupported source statement")
        sources.append(poly)
    for wire in source["booleans"]:
        value = atom(source_variable(wire))
        sources.append(plus(times(value, value), value, -1))

    def sparse(body):
        result = const(coefficient(body["constant"]))
        for scalar, wire in body["linear_terms"]:
            result = plus(result, atom(address(wire)), coefficient(scalar))
        for left, terms in body.get("quadratic_terms", []):
            for scalar, right in terms:
                result = plus(result, times(atom(address(left)), atom(address(right))), coefficient(scalar))
        return result

    lowered, copies = [], {}
    for layer in circuit["layers"]:
        for gate in layer["gates"] + layer["gates_with_external_connections"]:
            relation = gate["enforced_relation"]
            kind, body = next(iter(relation.items()))
            if kind == "CopyInBaseField":
                output, input_wire = address(body["output"]), address(body["input"])
                if output in copies:
                    raise ValueError("duplicate arithmetic copy producer")
                copies[output] = (input_wire, len(lowered))
                poly = plus(atom(output), atom(input_wire), -1)
            elif kind in ("MaxQuadratic", "EnforceSingleMaxQuadraticConstraint", "LinearBaseFieldRelation"):
                poly = sparse(body["input"])
                if "expression" in body and key(poly) != key(expression(body["expression"], address)):
                    raise ValueError("native sparse and structured gate fields disagree")
                if kind != "EnforceSingleMaxQuadraticConstraint":
                    poly = plus(atom(address(body["output"])), poly, -1)
            elif kind == "EnforceConstraintsMaxQuadratic":
                raise ValueError("batched arithmetic lowering needs a separate adapter")
            else:
                continue  # Explicit arithmetic-only slice; not a whole-GKR certificate.
            lowered.append(poly)

    def root(wire):
        visiting = set()
        while wire in copies:
            if wire in visiting:
                raise ValueError("cyclic native copy graph")
            visiting.add(wire)
            wire = copies[wire][0]
        return wire

    def reduce_copies(poly):
        current, combination = dict(poly), {}
        while True:
            selected = next(((monomial, value, wire) for monomial, value in current.items()
                             for wire in monomial if wire in copies), None)
            if selected is None:
                return cleaned(current), combination
            monomial, value, wire = selected
            root(wire)  # Check acyclicity before rewriting.
            input_wire, equation = copies[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): value}
            current = plus(current, times(factor, lowered[equation]), -1)
            combination[equation] = plus(combination.get(equation, {}), factor)

    normalized = {}
    reductions = []
    for index, poly in enumerate(lowered):
        reduced, combination = reduce_copies(poly)
        reductions.append(combination)
        normalized.setdefault(key(reduced), index)
    backwards = []
    selected = set()
    for index, poly in enumerate(sources):
        reduced, combination = reduce_copies(poly)
        if reduced:
            matched = normalized.get(key(reduced))
            if matched is None:
                raise ValueError(f"source obligation {index} has no native arithmetic identity")
            combination[matched] = plus(combination.get(matched, {}), const(1))
            for copy_index, factor in reductions[matched].items():
                combination[copy_index] = plus(combination.get(copy_index, {}), factor, -1)
        combination = {i: p for i, p in combination.items() if p}
        selected.update(combination)
        backwards.append(combination)
    selected = sorted(selected)
    local = {index: position for position, index in enumerate(selected)}

    root_variables = {}
    for wire in range(count):
        root_variables.setdefault(root(wire), wire)
    extension = []
    for wire in range(len(addresses)):
        if wire < count:
            extension.append(atom(wire))
        elif root(wire) in root_variables:
            extension.append(atom(root_variables[root(wire)]))
        else:
            extension.append({})  # Unused coordinates are explicitly zero.

    def substitute(poly):
        result = {}
        for monomial, value in poly.items():
            term = const(value)
            for wire in monomial:
                term = times(term, extension[wire])
            result = plus(result, term)
        return result

    source_keys = {key(poly): index for index, poly in enumerate(sources)}
    forwards = []
    for index in selected:
        translated = substitute(lowered[index])
        if not translated:
            forwards.append([])
        elif key(translated) in source_keys:
            forwards.append([[packed(const(1)), source_keys[key(translated)]]])
        else:
            raise ValueError(f"native arithmetic equation {index} needs a nontrivial forward identity")

    return {
        "format_version": 1,
        "addresses": addresses,
        "selected": selected,
        "extension": [packed(poly) for poly in extension],
        "backward": [[[packed(factor), local[index]] for index, factor in sorted(combo.items())]
                     for combo in backwards],
        "forward": forwards,
        "counts": {"source_variables": count, "lower_variables": len(addresses),
                   "source_obligations": len(sources), "native_arithmetic_relations": len(lowered),
                   "selected_relations": len(selected)},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pair", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    certificate = synthesis(json.loads(args.pair.read_text()))
    args.certificate.write_text(json.dumps(certificate, separators=(",", ":")) + "\n")
    print(json.dumps(certificate["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
