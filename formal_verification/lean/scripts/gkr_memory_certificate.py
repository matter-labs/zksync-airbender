#!/usr/bin/env python3
"""Untrusted memory occurrence selectors and copy-ideal witnesses.

No source fields, native payloads or replacement equations are certificate data.
The Lean importer must reconstruct both independently from the two captures.
"""
import argparse
import json
import os
import subprocess

from export_gkr_translations import FAMILIES, LEAN
from gkr_arithmetic_certificate import atom, const, packed, plus, times
from gkr_wiring_instances import CASES


def key(address):
    return json.dumps(address, sort_keys=True, separators=(",", ":"))


def synthesis(pair, snapshot):
    circuit, source = pair["circuit"], snapshot["semantic_inputs"]
    gates = [gate["enforced_relation"] for layer in circuit["layers"]
             for gate in layer["gates"] + layer["gates_with_external_connections"]]
    caches = [entry for layer in circuit["layers"] for entry in layer["cached_relations"]]
    addresses, indices = [], {}

    def locate(address):
        encoded = key(address)
        if encoded not in indices:
            indices[encoded] = len(addresses)
            addresses.append(address)
        return indices[encoded]

    for index in range(pair["source"]["num_variables"]):
        locate(circuit["placement_data"][str(index)])
    if len(addresses) != pair["source"]["num_variables"]:
        raise ValueError("aliased original memory source placements")
    for index in range(circuit["witness_layout"]["total_width"]):
        locate({"BaseLayerWitness": index})
    for index in range(circuit["memory_layout"]["total_width"]):
        locate({"BaseLayerMemory": index})
    for relation in gates:
        if "CopyInBaseField" in relation:
            for address in relation["CopyInBaseField"].values():
                locate(address)
    for name in ["InitsAndTeardownsLow", "InitsAndTeardownsHigh"]:
        locate({"VirtualSetup": name})
    arity = len(addresses)

    def variable(address):
        return atom(indices[key(address)])

    def original(index):
        if not 0 <= index < pair["source"]["num_variables"]:
            raise ValueError("memory source variable outside original scope")
        return variable(circuit["placement_data"][str(index)])

    def memory(index):
        return variable({"BaseLayerMemory": index})

    def word(representation, getter):
        if representation == "Zero":
            return [const(0), const(0)]
        kind, columns = next(iter(representation.items()))
        if kind == "U16Limbs":
            return [getter(index) for index in columns]
        if kind == "U8Limbs":
            return [plus(getter(columns[i]), getter(columns[i + 1]), 256) for i in (0, 2)]
        raise ValueError("unsupported source/native word representation")

    def fingerprint(fields):
        if len(fields) != 7:
            raise ValueError("memory fingerprint has wrong arity")
        result = plus(atom(arity + 6), fields[0])
        for index, field in enumerate(fields[1:]):
            result = plus(result, times(atom(arity + index), field))
        return result

    def native_fields(row):
        space_kind, space = next(iter(row["address_space"].items()))
        space = {"Constant": lambda: const(space), "IsRam": lambda: memory(space),
                 "IsRegister": lambda: plus(const(1), memory(space), -1)}[space_kind]()
        kind, data = next(iter(row["address"].items()))
        low, high = const(0), const(0)
        if kind in ("Constant", "ConstantU16"):
            low = const(data)
        elif kind == "U16Space":
            low = memory(data)
        elif kind == "U32Space":
            low, high = [memory(index) for index in data]
        elif kind == "U32SpaceSpecialIndirect":
            low, high = memory(data["low_base"]), memory(data["high"])
            if data["low_dynamic_offset"] is not None:
                coefficient, column = data["low_dynamic_offset"]
                low = plus(low, memory(column), coefficient)
            low = plus(low, const(data["low_offset"]))
        else:
            raise ValueError("unsupported native memory address")
        timestamp = [const(0), const(0)] if row["timestamp"] == "Zero" else [memory(i) for i in row["timestamp"]["Normal"]]
        if row["timestamp"] != "Zero":
            timestamp[0] = plus(timestamp[0], const(row["timestamp_offset"]))
        return [space, low, high, *timestamp, *word(row["value"], memory)]

    def history(query):
        metadata = next(iter(circuit["memory_layout"]["ram_access_sets"][query].values()))
        return [memory(i) for i in metadata["read_timestamp"]]

    def indirect(base, dynamic, offset):
        low, high = base
        if dynamic is not None:
            coefficient, index, _access_index = dynamic
            low = plus(low, original(index), coefficient)
        return [plus(low, const(offset)), high]

    reads, writes = [], []

    def request(space, address, timestamp, old, new, write_timestamp, offset):
        reads.append([space, *address, *timestamp, *old])
        writes.append([space, *address, plus(write_timestamp[0], const(offset)), write_timestamp[1], *new])

    executor, delegation = source["executor_machine_state"], source["delegation_circuit_state"]
    if executor is not None:
        base_timestamp = [original(i) for i in executor["cycle_start_state"]["timestamp"]]
        for query in source["memory_queries"]:
            kind, data = next(iter(query.items()))
            space = const(0)
            if kind == "ConstantRegister":
                address = [const(data["reg_idx"]), const(0)]
            elif kind == "RegisterOnly":
                address = [original(data["reg_idx"]), const(0)]
            elif kind == "RegisterOrRam":
                tag, boolean = next(iter(data["is_register"].items()))
                space = const(0 if boolean else 1) if tag == "Constant" else (
                    plus(const(1), original(boolean), -1) if tag == "Is" else original(boolean))
                address = [original(i) for i in data["address"]]
            elif kind == "RamIndirect":
                space = const(1)
                address = indirect([original(i) for i in data["base_address"]], data["variable_offset"], data["constant_offset"])
            else:
                raise ValueError("unsupported original memory request")
            request(space, address, [original(i) for i in data["read_timestamp"]], word(data["read_value"], original),
                    word(data["write_value"], original), base_timestamp, data["local_timestamp_in_cycle"])
        for destination, state in ((reads, "cycle_start_state"), (writes, "cycle_end_state")):
            destination.append([const(2), const(0), const(0), *[original(i) for i in executor[state]["timestamp"]],
                                *[original(i) for i in executor[state]["pc"]]])
    elif delegation is not None:
        base_timestamp = [original(i) for i in delegation["invocation_timestamp"]]
        for access in source["register_and_indirect_accesses"]:
            kind, data = next(iter(access["register_access"].items()))
            old = [original(i) for i in data["read_value"]]
            new = old if kind == "Read" else [original(i) for i in data["write_value"]]
            request(const(0), [const(access["register_index"]), const(0)], history(len(reads)), old, new, base_timestamp, 2)
            for raw in access["indirect_accesses"]:
                kind, data = next(iter(raw.items()))
                before = [original(i) for i in data["read_value"]]
                after = before if kind == "Read" else [original(i) for i in data["write_value"]]
                request(const(1), indirect(old, data["variable_dependent"], data["offset_constant"]),
                        history(len(reads)), before, after, base_timestamp, 2)
        marker = [const(0), const(delegation["delegation_type"]), const(0)]
        reads.append([*marker, *base_timestamp, const(0), const(0)])
        writes.append([*marker, const(0), const(0), const(0), const(0)])
    else:
        raise ValueError("source memory state missing")

    virtual = [variable({"VirtualSetup": name}) for name in ("InitsAndTeardownsLow", "InitsAndTeardownsHigh")]
    initial_values, final_values = [], []
    for index in range(2 * snapshot["configuration"]["inline_init_teardown_pairs"]):
        address = [virtual[0], plus(virtual[1], const(index * 2 ** (snapshot["configuration"]["trace_len_log2"] + 2 - 16)))]
        timestamps, values = circuit["memory_layout"]["teardown_sets"][index]
        initial_values.append([const(1), *address, const(0), const(0), const(0), const(0)])
        final_values.append([const(1), *address, *[variable(i) for i in timestamps], *[variable(i) for i in values]])
    source_groups = {"memoryRead": reads, "memoryWrite": writes,
                     "initializationRead": final_values, "initializationWrite": initial_values}

    registry, environment, masks = [], {}, {}
    memory_caches = {key(address): (index, relation["MemoryTuple"]) for index, (address, relation) in enumerate(caches)
                     if "MemoryTuple" in relation}

    def leaf(fields, locator, expansion=None):
        index = len(registry)
        registry.append({"locator": locator, "expansion": expansion or [], "polynomial": fingerprint(fields)})
        return index

    def cached(address, locator):
        definition, row = memory_caches[key(address)]
        return leaf(native_fields(row), locator, [definition])

    for gate_index, relation in enumerate(gates):
        kind, data = next(iter(relation.items()))
        if kind in ("InitialGrandProductFromCaches", "InitialGrandProductWithoutCaches"):
            environment[key(data["output"])] = [cached(value, [gate_index, i]) if kind.endswith("FromCaches") else
                leaf(native_fields(value), [gate_index, i]) for i, value in enumerate(data["input"])]
        elif kind == "MaterializeGrandProductTermExpression":
            environment[key(data["output"])] = [leaf(native_fields(data["input"]), [gate_index, 0])]
        elif kind == "CopyInExtensionField":
            if key(data["input"]) in memory_caches:
                environment[key(data["output"])] = [cached(data["input"], [gate_index, 0])]
            elif key(data["input"]) in environment:
                environment[key(data["output"])] = list(environment[key(data["input"])])
                if key(data["input"]) in masks:
                    masks[key(data["output"])] = masks[key(data["input"])]
        elif kind == "TrivialProduct":
            environment[key(data["output"])] = sum((environment[key(address)] for address in data["input"]), [])
        elif kind == "MaskIntoIdentityProduct":
            environment[key(data["output"])] = list(environment[key(data["input"])])
            masks[key(data["output"])] = data["mask"]
        elif kind == "InitsOrTeardownsInitialPair":
            ids = []
            for side, set_index in enumerate(data["set_idxes"]):
                address = [variable(data["setup"][0]), plus(variable(data["setup"][1]), const(
                    set_index * 2 ** (circuit["trace_len"].bit_length() - 1 + circuit["memory_layout"]["inits_and_teardowns_word_bits"] - 16)))]
                state = data["timestamp_and_value"]
                timestamps, values = [const(0), const(0)], [const(0), const(0)]
                if state != "Init":
                    tag = "lhs" if side == 0 else "rhs"
                    timestamps = [memory(i) for i in state["Teardown"][tag + "_timestamp"]]
                    values = [memory(i) for i in state["Teardown"][tag + "_value"]]
                ids.append(leaf([const(1), *address, *timestamps, *values], [gate_index, side]))
            environment[key(data["output"])] = ids

    equations, copy_map = [], {}
    for relation in gates:
        if "CopyInBaseField" in relation:
            data = relation["CopyInBaseField"]
            output, source_input = indices[key(data["output"])], indices[key(data["input"])]
            copy_map[output] = len(equations)
            equations.append(plus(atom(output), atom(source_input), -1))

    def reduce(poly):
        poly, witness = dict(poly), {}
        while True:
            choice = next(((monomial, scalar, wire) for monomial, scalar in poly.items()
                           for wire in monomial if wire in copy_map), None)
            if choice is None:
                return poly, witness
            monomial, scalar, wire = choice
            index = copy_map[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): scalar}
            poly = plus(poly, times(factor, equations[index]), -1)
            witness[index] = plus(witness.get(index, {}), factor)

    groups = {}
    for kind, outputs in circuit["global_output_map"].items():
        if kind not in ("PermutationProduct", "InitsAndTeardownsProduct"):
            continue
        stem = "memory" if kind == "PermutationProduct" else "initialization"
        for side, output in zip(("Read", "Write"), outputs, strict=True):
            name = stem + side
            bank = [fingerprint(row) for row in source_groups[name]]
            canonical = [reduce(poly)[0] for poly in bank]
            used, labels, witnesses = set(), [], []
            leaves = environment[key(output)]
            for index in leaves:
                actual = registry[index]["polynomial"]
                reduced = reduce(actual)[0]
                selected = next((i for i, source_poly in enumerate(canonical) if i not in used and source_poly == reduced), None)
                if selected is None:
                    raise ValueError(f"actual {name} primitive {index} does not match an unused original source request")
                used.add(selected)
                labels.append(selected)
                remainder, witness = reduce(plus(bank[selected], actual, -1))
                if remainder:
                    raise ValueError("source memory fingerprint identity failed")
                witnesses.append([[packed(poly), ordinal] for ordinal, poly in sorted(witness.items()) if poly])
            if sorted(labels) != list(range(len(bank))):
                raise ValueError("source memory occurrence coverage incomplete")
            mask = None
            if stem == "memory":
                predicate = masks[key(output)]
                execute = executor["execute"] if executor is not None else delegation["execute"]
                remainder, mask_witness = reduce(plus(original(execute), variable(predicate), -1))
                if remainder:
                    raise ValueError("native execution mask is not the original source predicate modulo copies")
                mask = {"address": predicate, "witness": [[packed(poly), ordinal]
                        for ordinal, poly in sorted(mask_witness.items()) if poly]}
            groups[name] = {"native_leaves": leaves, "source_labels": labels, "witnesses": witnesses, "mask": mask}
    return {"format_version": 1, "addresses": addresses,
            "leaves": [{"native_leaf": i, "locator": row["locator"], "expansion": row["expansion"]} for i, row in enumerate(registry)],
            "groups": groups, "counts": {"registry": len(registry), "occurrences": sum(len(g["native_leaves"]) for g in groups.values()),
                                          "nonempty_witnesses": sum(bool(w) for g in groups.values() for w in g["witnesses"])}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, action="append")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    root = LEAN / "artifacts/compiler"
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ("uncached", "cached"):
            name = family + "-" + mode
            result = synthesis(json.loads((root / (name + ".json")).read_text()),
                               json.loads((root / (name + "-source.json")).read_text()))
            case = stem + mode.title()
            module = "GKRProtocol.MemoryNative." + case
            if args.write or args.check:
                destination = LEAN / "GKRProtocol/MemoryNative" / (case + ".lean")
                selectors = json.dumps(json.dumps(result, separators=(",", ":")))
                content = (
                    "import GKRProtocol.MemoryImport\n"
                    f"import GKRProtocol.ProductNative.{case}\n\n"
                    f"namespace Airbender.Compiler.MemoryNative.{case}\n"
                    "open Airbender Airbender.Compiler\n"
                    "set_option warningAsError true\n"
                    "set_option Elab.async false\n"
                    "set_option maxRecDepth 32768\n"
                    "set_option maxHeartbeats 4000000\n\n"
                    f'import_source_memory native from "artifacts/compiler/{name}.json"\n'
                    f'  source "artifacts/compiler/{name}-source.json"\n'
                    f"  selectors {selectors}\n"
                    "  word_bits 2\n"
                    f"  native_model Airbender.Compiler.ProductNative.{case}.native\n"
                    f"  typing Airbender.Compiler.ConsumerNative.{case}.native.typing\n\n"
                    f"end Airbender.Compiler.MemoryNative.{case}\n")
                if args.check and (not destination.exists() or destination.read_text() != content):
                    raise ValueError(f"source memory selectors changed: {case}")
                if args.write and (not destination.exists() or destination.read_text() != content):
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_text(content)
            print(name, result["counts"], flush=True)
            if args.build:
                subprocess.run(["lake", "--no-cache", "build", "+" + module + ":olean"],
                               cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS="1"), check=True)


if __name__ == "__main__":
    main()
