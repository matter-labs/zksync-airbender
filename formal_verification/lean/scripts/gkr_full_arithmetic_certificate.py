#!/usr/bin/env python3
"""Untrusted full base-field witness extension certificates.

Every native base-field arithmetic gate, scalar cache and scalar materializer is
included. Source obligations are original equations plus independently derived
clock/borrow assertions. Lean reconstructs both lists; certificates contain only
addresses, extension polynomials and ideal witnesses. Primitive history contracts
must discharge the source helper assertions before claiming complete extension.
"""
import argparse
import json
import os
import subprocess

from gkr_arithmetic_certificate import synthesis as old_synthesis, PRIME, atom, const, plus, times, expression, coefficient, key, packed
from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES

def synthesize(pair,snapshot):
    base=old_synthesis(pair)
    circuit=pair['circuit']; source=pair['source']; semantic=snapshot['semantic_inputs']; n=source['num_variables']
    addresses=base['addresses'];ids={json.dumps(a,sort_keys=True):i for i,a in enumerate(addresses)}
    def addr(a):
        k=json.dumps(a,sort_keys=True)
        if k not in ids: ids[k]=len(addresses);addresses.append(a)
        return ids[k]
    initial={i:atom(i) for i in range(n)};free=[]
    for kind,width in [('BaseLayerWitness',circuit['witness_layout']['total_width']),('BaseLayerMemory',circuit['memory_layout']['total_width'])]:
        for i in range(width):
            a={kind:i};wire=addr(a)
            if wire not in initial:
                initial[wire]=atom(n+len(free));free.append(a)
    def original(i):return atom(i)
    def at(a):return initial[addr(a)]
    def fields(word):return [original(i) for i in word]
    source_polys=[]
    for stmt in source['statements']:
        kind,data=next(iter(stmt.items())); p=expression(data['expr'],lambda x:x)
        if kind=='Define':p=plus(atom(data['dst']),p,-1)
        source_polys.append(p)
    for b in source['booleans']:source_polys.append(plus(times(atom(b),atom(b)),atom(b),-1))
    borrows=[at(x['intermediate_borrow']) for x in circuit['aux_layout_data']['shuffle_ram_timestamp_comparison_aux_vars']]
    if semantic['executor_machine_state'] is not None:
        state=semantic['executor_machine_state']; lo,hi=fields(state['cycle_start_state']['timestamp']);flo,fhi=fields(state['cycle_end_state']['timestamp'])
        carry=times(const(pow(524288,-1,PRIME)),plus(plus(lo,const(4)),flo,-1))
        source_polys.extend([plus(times(carry,carry),carry,-1),plus(plus(fhi,hi,-1),carry,-1)])
    source_polys.extend(plus(times(b,b),b,-1) for b in borrows)
    source_index={key(p):i for i,p in enumerate(source_polys)}
    source_negative={key(plus({},p,-1)):i for i,p in enumerate(source_polys)}
    def sparse(data):
        p=const(coefficient(data['constant']))
        for c,a in data['linear_terms']:p=plus(p,atom(addr(a)),coefficient(c))
        for a,terms in data.get('quadratic_terms',[]):
            for c,b in terms:p=plus(p,times(atom(addr(a)),atom(addr(b))),coefficient(c))
        return p
    cacheDefinitions={}
    for layer in circuit['layers']:
        for output,cache in layer['cached_relations']:
            if 'SingleColumnLookup' in cache:
                cacheDefinitions[addr(output)]=sparse(cache['SingleColumnLookup']['relation']['input'])
    for i,a in enumerate(addresses):
        if i not in initial and next(iter(a)) in ['Setup','VirtualSetup']:
            initial[i]=atom(n+len(free));free.append(a)
    gates=[(out,poly) for out,poly in cacheDefinitions.items()]
    for layer in circuit['layers']:
        for g in layer['gates']+layer['gates_with_external_connections']:
            kind,data=next(iter(g['enforced_relation'].items()))
            if kind=='CopyInBaseField':gates.append((addr(data['output']),atom(addr(data['input']))))
            elif kind=='MaterializeSingleLookupInput':gates.append((addr(data['output']),sparse(data['input']['input'])))
            elif kind in ['LinearBaseFieldRelation','MaxQuadratic','EnforceSingleMaxQuadraticConstraint']:
                p=sparse(data['input']);out=None if kind=='EnforceSingleMaxQuadraticConstraint' else addr(data['output'])
                gates.append((out,p))
    def sub(p):
        result={}
        for monomial,c in p.items():
            term=const(c)
            for a in monomial:
                if a not in initial:
                    if a not in cacheDefinitions:raise ValueError(('unassigned',addresses[a]))
                    initial[a]=sub(cacheDefinitions[a])
                term=times(term,initial[a])
            result=plus(result,term)
        return result
    forward=[];unmatched=[]
    for index,(out,p) in enumerate(gates):
        evaluated=sub(p)
        if out is None: residual=evaluated
        elif out in initial: residual=plus(initial[out],evaluated,-1)
        else:initial[out]=evaluated;residual={}
        if not residual:forward.append([])
        elif key(residual) in source_index:forward.append([[packed(const(1)),source_index[key(residual)]]])
        elif key(residual) in source_negative:forward.append([[packed(const(-1)),source_negative[key(residual)]]])
        else:unmatched.append((index,out,packed(residual)));forward.append(None)
    if unmatched:
        raise ValueError(f'full native arithmetic has unmatched forward identities: {unmatched[:1]}')
    # Derive the converse from actual native definitions and assertions.
    # Source polynomials are renamed into native input coordinates; neither side
    # of a relation is serialized into the certificate.
    input_coordinates = [addr(value) for value in addresses[:n] + free]
    input_set = set(input_coordinates)
    lowered = [poly if output is None else plus(atom(output), poly, -1) for output, poly in gates]
    definitions = {output: (poly, i) for i, (output, poly) in enumerate(gates)
                   if output is not None and output not in input_set}

    def reduce_definitions(poly):
        poly, witness = dict(poly), {}
        for _ in range(100000):
            choice = next(((monomial, scalar, wire) for monomial, scalar in poly.items()
                           for wire in monomial if wire in definitions), None)
            if choice is None:
                return poly, {i: value for i, value in witness.items() if value}
            monomial, scalar, wire = choice
            _, ordinal = definitions[wire]
            rest = list(monomial)
            rest.remove(wire)
            factor = {tuple(rest): scalar}
            poly = plus(poly, times(factor, lowered[ordinal]), -1)
            witness[ordinal] = plus(witness.get(ordinal, {}), factor)
        raise ValueError("nonterminating native base definition expansion")

    normalized, reductions = {}, []
    for i, relation in enumerate(lowered):
        reduced, witness = reduce_definitions(relation)
        reductions.append(witness)
        if reduced:
            normalized.setdefault(key(reduced), (i, 1))
            normalized.setdefault(key(plus({}, reduced, -1)), (i, -1))
    backwards = []
    for ordinal, source_poly in enumerate(source_polys):
        renamed = {}
        for monomial, scalar in source_poly.items():
            term = const(scalar)
            for wire in monomial:
                term = times(term, atom(input_coordinates[wire]))
            renamed = plus(renamed, term)
        reduced, witness = reduce_definitions(renamed)
        if reduced:
            if key(reduced) not in normalized:
                raise ValueError(f"source obligation {ordinal} lacks an actual native backward identity")
            matched, sign = normalized[key(reduced)]
            witness[matched] = plus(witness.get(matched, {}), const(sign))
            for i, factor in reductions[matched].items():
                witness[i] = plus(witness.get(i, {}), factor, -sign)
        backwards.append([[packed(value), i] for i, value in sorted(witness.items()) if value])
    # Put all logical/oracle inputs first. Preservation is then a structural
    # identity; the certificate only supplies computed-coordinate extensions.
    input_addresses = addresses[:n] + free
    input_keys = {json.dumps(address, sort_keys=True) for address in input_addresses}
    ordered = input_addresses + [address for address in addresses
                                 if json.dumps(address, sort_keys=True) not in input_keys]
    old_coordinates = {json.dumps(address, sort_keys=True): i for i, address in enumerate(addresses)}
    permutation = {old_coordinates[json.dumps(address, sort_keys=True)]: i
                   for i, address in enumerate(ordered)}
    renamed_backward = []
    for proof in backwards:
        renamed_backward.append([[[[scalar, sorted(permutation[wire] for wire in monomial)]
                                   for scalar, monomial in polynomial], relation]
                                  for polynomial, relation in proof])
    return {"format_version": 1, "inputs": input_addresses, "addresses": ordered,
            "extension": [packed(initial.get(old_coordinates[json.dumps(address, sort_keys=True)], {}))
                          for address in ordered], "forward": forward, "backward": renamed_backward,
            "counts": {"original_variables": n, "input_variables": len(input_addresses),
                       "source_obligations": len(source_polys), "relations": len(gates)}}



def modules(name, case, result):
    prefix = "GKRProtocol.FullArithmeticNative." + case
    namespace = "Airbender.Compiler.FullArithmeticNative." + case
    dimensions = (f'inputs {len(result["inputs"])} variables {len(result["addresses"])} '
                  f'sources {result["counts"]["source_obligations"]} gates {result["counts"]["relations"]}')
    selectors = json.dumps(json.dumps(result, separators=(",", ":")))

    def wrap(imports, command):
        return ("".join("import " + item + "\n" for item in imports) + "\n"
                f"namespace {namespace}\n"
                "open Airbender Airbender.Compiler\n"
                "set_option warningAsError true\n"
                "set_option Elab.async false\n"
                "set_option maxRecDepth 32768\n"
                "set_option maxHeartbeats 4000000\n\n" + command + "\n\n"
                f"end {namespace}\n")

    foundation = prefix + "Foundation"
    result_modules = [(foundation, wrap(["GKRProtocol.FullArithmeticImport"],
        f'import_full_compiler_arithmetic native from "artifacts/compiler/{name}.json"\n'
        f'  source "artifacts/compiler/{name}-source.json"\n  selectors {selectors}'))]
    parts = []
    counts = [len(result["addresses"]), result["counts"]["relations"], result["counts"]["source_obligations"]]
    for phase, (label, count) in enumerate(zip(["Unique", "Forward", "Backward"], counts, strict=True)):
        for part, start in enumerate(range(0, count, 32)):
            module = prefix + label + "Part" + str(part)
            parts.append(module)
            result_modules.append((module, wrap([foundation],
                f'check_full_compiler_arithmetic native {dimensions} phase {phase} '
                f'start {start} stop {min(start + 32, count)}')))
    result_modules.append((prefix, wrap([foundation] + parts,
        f'finalize_full_compiler_arithmetic native {dimensions}')))
    return result_modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, action="append")
    parser.add_argument("--mode", choices=("uncached", "cached"), action="append")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    root = LEAN / "artifacts/compiler"
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if args.family and family not in args.family:
            continue
        for mode in ("uncached", "cached"):
            if args.mode and mode not in args.mode:
                continue
            name, case = family + "-" + mode, stem + mode.title()
            result = synthesize(json.loads((root / (name + ".json")).read_text()),
                                json.loads((root / (name + "-source.json")).read_text()))
            targets = modules(name, case, result)
            for module, content in targets:
                destination = LEAN / (module.replace(".", "/") + ".lean")
                if args.check and (not destination.exists() or destination.read_text() != content):
                    raise ValueError(f"full arithmetic selectors changed: {module}")
                if args.write and (not destination.exists() or destination.read_text() != content):
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_text(content)
            print(name, result["counts"], len(targets), "sequential proof modules", flush=True)
            if args.build:
                # Build each foundation/shard before its root. A single Lake
                # request for the root could launch multiple Lean workers.
                for module, _ in targets:
                    subprocess.run(["lake", "--no-cache", "build", "+" + module + ":olean"],
                                   cwd=LEAN, env=dict(os.environ, LEAN_NUM_THREADS="1"), check=True)


if __name__ == "__main__":
    main()
