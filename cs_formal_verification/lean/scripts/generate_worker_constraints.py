#!/usr/bin/env python3
"""Generate checked native-worker lookup bindings from the retained circuit inputs."""
from pathlib import Path
import json
from check_compiler_captures import FAMILIES, cached_layout
from generate_worker_selectors import selectors, WORKERS, address_key

ROOT = Path(__file__).resolve().parents[1]
P = 2013265921
INVERSE = 943718400
LEAN_FAMILY = {"Bigint": "bigint", "BlakeG": "blakeG", "BlakeRound": "blakeRound",
               "KeccakColumnParity": "columnParity", "KeccakThetaRho": "thetaRho", "KeccakChi5": "chi5"}


def append_lists(segments):
    """Keep the list form equal to the recursive membership proof form."""
    result = segments[-1]
    for segment in reversed(segments[:-1]):
        result = f"({segment} ++ {result})"
    return result


def coefficient(value):
    return f"⟨⟨{value}, by decide⟩⟩"


def address(value):
    kind, item = next(iter(value.items()))
    if kind in ("BaseLayerMemory", "BaseLayerWitness", "Setup", "ScratchSpace"):
        return f"(.{kind} {item})"
    if kind in ("InnerLayer", "Cached"):
        return f"(.{kind} {item['layer']} {item['offset']})"
    raise ValueError(f"Unsupported source address: {value}")


def linear(value):
    terms = ", ".join(f"({coefficient(c)}, {address(a)})" for c, a in value["linear_terms"])
    return f"⟨#[{terms}], {coefficient(value['constant'])}⟩"


def operand(row):
    columns = row["encoding"]["columns"]
    request = row["request"] or 0
    if row["encoding"]["kind"] == "vector":
        if any("linear" not in c for c in columns):
            raise ValueError("A source worker vector must retain its affine columns")
        return f"⟨.one, .vector ⟨#[{', '.join(linear(c['linear']) for c in columns)}], {request}⟩⟩"
    if "cell" in columns[0]:
        return f"⟨.one, .address {address(columns[0]['cell'])}⟩"
    return f"⟨.one, .scalar ⟨{linear(columns[0]['linear'])}, {request}⟩⟩"


def load(name):
    family = WORKERS[name]
    circuit = json.loads(cached_layout(FAMILIES[family]).read_text())
    native = selectors(circuit)
    placements = {address_key(a): int(i) for i, a in circuit["placement_data"].items()}
    positions = {int(i): position for position, i in enumerate(sorted(circuit["placement_data"], key=int))}

    def logical(value):
        if "ScratchSpace" in value:
            value = circuit["scratch_space_mapping_rev"][str(value["ScratchSpace"])]
        return placements[address_key(value)]

    def normalized(column):
        if "cell" in column:
            return ((logical(column["cell"]), 1), (-1, 0))
        relation = column["linear"]
        terms = {}
        for scalar, physical in relation["linear_terms"]:
            index = logical(physical)
            terms[index] = (terms.get(index, 0) + scalar * INVERSE) % P
        return tuple(sorted((i, v) for i, v in terms.items() if v)) + ((-1, relation["constant"] * INVERSE % P),)

    def native_key(row):
        return row["group"], tuple(normalized(col) for col in row["encoding"]["columns"])

    source = []
    for group, rows in [(1, circuit["range_check_16_lookup_expressions"]),
                        (2, circuit["timestamp_range_check_lookup_expressions"]),
                        (0, circuit["generic_lookups"])]:
        for index, row in enumerate(rows):
            columns = [{"linear": row["input"]}] if group else [{"linear": col} for col in row["columns"]]
            source.append({"group": group, "index": index, "columns": columns,
                           "key": (group, tuple(normalized(col) for col in columns))})
    source_by_key = {}
    native_by_key = {}
    for i, row in enumerate(source):
        source_by_key.setdefault(row["key"], []).append(i)
    for i, row in enumerate(native):
        native_by_key.setdefault(native_key(row), []).append(i)
    if any(native_key(row) not in source_by_key for row in native):
        raise ValueError("Native query has no source expression")
    if any(row["key"] not in native_by_key for row in source):
        raise ValueError("Source query has no native operand")
    for row in native:
        row["source"] = source_by_key[native_key(row)][0]
    for row in source:
        row["native"] = native_by_key[row["key"]][0]
    return circuit, native, source, logical, positions


def source_expression(column, logical):
    if "cell" in column:
        return f"(.Var {logical(column['cell'])})"
    relation = column["linear"]
    terms = [f"(.Constant {coefficient(relation['constant'])})"]
    terms += [f"(.Product #[.Constant {coefficient(c)}, .Var {logical(a)}])"
              for c, a in relation["linear_terms"]]
    return f"(.Sum #[{', '.join(terms)}])"


def fields_theorem(name, index, circuit, native, source, logical, positions):
    row = native[index]
    source_row = source[row["source"]]
    capture = f"Captures.{name}.imported.circuit"
    physical = {}
    for col in row["encoding"]["columns"]:
        addresses = [col["cell"]] if "cell" in col else [a for _, a in col["linear"]["linear_terms"]]
        for a in addresses:
            physical[logical(a)] = a
    lines = [f"/-- The native tuple uses exactly the source lookup columns. -/",
             f"theorem fields{index} (physical : GKRAddress → F) (logical : Nat → F)",
             f"    (agreement : PlacementAgreement ({capture}) physical logical) :",
             f"    operand{index}.input.fields physical = sourceFields{index} logical := by"]
    for variable, a in physical.items():
        lines += [f"  have p{variable} : physical {address(a)} = logical {variable} :=",
                  f"    placed agreement (position := {positions[variable]}) (by kernel_rfl)"]
    lines += [f"  simp only [operand{index}, NativeLookups.Input.fields, sourceFields{index}" +
              (", List.map_cons, List.map_nil]" if row["encoding"]["kind"] == "vector" else "]")]
    native_linear = any("linear" in col for col in row["encoding"]["columns"])
    rules = (["linear", "← Array.foldl_toList", "List.foldl_cons", "List.foldl_nil"] if native_linear else [])
    rules += ["Import.expression", "Import.sum", "Import.product", "Import.constant", "Expression.eval", "Verification.environment"]
    lines += ["  simp only [" + ", ".join(rules) + "]"]
    if physical:
        lines += ["  rw [" + ", ".join(f"p{v}" for v in physical) + "]"]
    if native_linear:
        lines += ["  simp only [coefficient_value]"]
    lines += ["  norm_num [Artifact.signedCoefficient, Coefficient.canonical, Fp.ofNat, montgomeryInverse, babyBearModulus]", ""]
    return "\n".join(lines)



def lean_header(name, imports):
    return ("module\n" + "\n".join("public import " + item for item in imports) +
            "\n\n@[expose] public section\nset_option warningAsError true\n" +
            f"namespace Airbender.Compiler.WorkerConstraints.{name}\n" +
            "open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups\n" +
            "set_option maxRecDepth 32768\n\n")


def emit_family(name):
    circuit, native, source, logical, positions = load(name)
    family = LEAN_FAMILY[name]
    namespace = f"Proven.Compiler.WorkerConstraints.{name}"
    directory = ROOT / "proven/Proven/Compiler/WorkerConstraints" / name
    ending = f"\nend Airbender.Compiler.WorkerConstraints.{name}\n"
    outputs = {}
    data_chunk = 12
    field_chunk = 8
    data_parts = []
    for start in range(0, len(native), data_chunk):
        part = f"Queries{start // data_chunk:03d}"
        data_parts.append(f"{namespace}.{part}")
        text = lean_header(name, ["Proven.Compiler.WorkerConstraints.Values",
                                 "Proven.Compiler.WorkerConstraints.Setup", "Proven.KernelRfl"])
        for i in range(start, min(start + data_chunk, len(native))):
            row = native[i]
            source_row = source[row["source"]]
            expressions = [f"Import.expression {source_expression(col, logical)}" for col in source_row["columns"]]
            terms = ", ".join(f"({expression}).eval (Verification.environment logical)" for expression in expressions)
            table = f"WorkerConstraints.setupTable .{family}" if row["group"] == 0 else (
                "Verification.range16Table" if row["group"] == 1 else "Trace.timestampTable")
            text += f"/-- One actual resolved primitive operand. -/\nnoncomputable def operand{i} : NativeLookups.Operand := {operand(row)}\n\n"
            text += f"/-- The retained logical expressions of the same query. -/\nnoncomputable def sourceExpressions{i} : Vector (Airbender.Expression F) {len(expressions)} := #v[{', '.join(expressions)}]\n\n"
            text += f"/-- The query uses its reviewed source table. -/\nnoncomputable def sourceLookup{i} : Lookup F := ⟨({table}).toRaw, sourceExpressions{i}⟩\n\n"
            text += f"/-- Evaluated source fields retain their complete order. -/\nnoncomputable def sourceFields{i} (logical : Nat → F) : List F := [{terms}]\n\n"
            text += f"theorem source_values{i} (logical : Nat → F) :\n    (sourceExpressions{i}.map (Verification.environment logical)).toList = sourceFields{i} logical := by kernel_rfl\n\n"
            if row["group"] == 0:
                tag = source_row["columns"][-1]["linear"]
                assert not tag["linear_terms"]
                tag_value = tag["constant"] * INVERSE % P
                assert tag_value != 0
                text += f"/-- The fixed nonzero tag excludes native zero padding. -/\ntheorem source_tag{i} (logical : Nat → F) :\n    ((sourceFields{i} logical)[{len(expressions) - 1}]?).getD 0 ≠ 0 := by\n  change ({tag_value} : F) ≠ 0\n  decide +kernel\n\n"
                text += f"/-- The reviewed query and public native table have the same members. -/\ntheorem source_semantics{i} (logical : Nat → F) :\n    (sourceLookup{i}).Contains (Verification.environment logical) ↔\n      ∃ index, sourceFields{i} logical = NativeWorkerSetup.rows .{family} 0 index := by\n  have tag : (((sourceExpressions{i}.map (Verification.environment logical)).toList)[width .{family} - 1]?).getD 0 ≠ 0 := by\n    rw [source_values{i}]\n    exact source_tag{i} logical\n  have equivalent := generic_lookup_refinement .{family} sourceExpressions{i} logical tag\n  constructor\n  · intro accepted\n    obtain ⟨index, same⟩ := equivalent.mp accepted\n    exact ⟨index, (source_values{i} logical).symm.trans same⟩\n  · rintro ⟨index, same⟩\n    exact equivalent.mpr ⟨index, (source_values{i} logical).trans same⟩\n\n"
            else:
                scalar = expressions[0]
                helper = "range16_refinement" if row["group"] == 1 else "timestamp_refinement"
                unfold = "Verification.range16" if row["group"] == 1 else "Trace.timestampLookup"
                text += f"/-- The reviewed scalar query and public native range have the same members. -/\ntheorem source_semantics{i} (logical : Nat → F) :\n    (sourceLookup{i}).Contains (Verification.environment logical) ↔\n      ∃ index, sourceFields{i} logical = NativeWorkerSetup.rows .{family} {row['group']} index := by\n  simpa only [sourceLookup{i}, sourceExpressions{i}, sourceFields{i}, {unfold}] using\n    {helper} .{family} ({scalar}) logical\n\n"
        outputs[directory / f"{part}.lean"] = text + ending
    field_parts = []
    for start in range(0, len(native), field_chunk):
        part = f"Fields{start // field_chunk:03d}"
        field_parts.append(f"{namespace}.{part}")
        needed = sorted({i // data_chunk for i in range(start, min(start + field_chunk, len(native)))})
        text = lean_header(name, [f"{namespace}.Queries{i:03d}" for i in needed])
        for i in range(start, min(start + field_chunk, len(native))):
            text += fields_theorem(name, i, circuit, native, source, logical, positions) + "\n"
            text += f"/-- Source membership is equivalent to the actual placed native tuple membership. -/\ntheorem refinement{i} (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical) :\n    (sourceLookup{i}).Contains (Verification.environment logical) ↔\n      ∃ index, operand{i}.input.fields physical = NativeWorkerSetup.rows .{family} {native[i]['group']} index := by\n  rw [fields{i} physical logical agreement]\n  exact source_semantics{i} logical\n\n"
        outputs[directory / f"{part}.lean"] = text + ending
    text = lean_header(name, data_parts + ["Mathlib.Tactic.FinCases"])
    groups = [[i for i, row in enumerate(native) if row["group"] == group] for group in range(3)]
    for group, indices in enumerate(groups):
        for start in range(0, len(indices), 16):
            entries = ", ".join(f"operand{i}.input.fields physical" for i in indices[start:start + 16])
            text += f"/-- One complete segment of native tuples in selector order. -/\nnoncomputable def tuple{group}_{start // 16:03d} (physical : GKRAddress → F) : List (List F) := [{entries}]\n\n"
    terms = [append_lists([f"tuple{group}_{start // 16:03d} physical" for start in range(0, len(indices), 16)] + ["[]"]) for group, indices in enumerate(groups)]
    text += f"/-- Every complete native tuple, in the selector order of each group. -/\nnoncomputable def tuples (physical : GKRAddress → F) (group : Fin 3) : List (List F) :=\n  ([{', '.join(terms)}] : List (List (List F))).get group\n\n"
    text += f"/-- The literal tuples are exactly the actual native requests. -/\ntheorem binding (physical : GKRAddress → F) (group : Fin 3) :\n    NativeLookups.requests (circuitFor .{family}) (selectorsFor .{family}) physical group = .ok (tuples physical group) := by\n  fin_cases group <;> kernel_rfl\n\n"
    outputs[directory / "Tuples.lean"] = text + ending
    for start in range(0, len(native), 16):
        text = lean_header(name, [f"{namespace}.Tuples", "Proven.KernelExact"])
        for i in range(start, min(start + 16, len(native))):
            row = native[i]
            group = row["group"]
            position = groups[group].index(i)
            segment = position // 16
            local_position = position % 16
            segment_length = min(16, len(groups[group]) - 16 * segment)
            member = f"List.getElem_mem (l := tuple{group}_{segment:03d} physical) (n := {local_position}) (by change {local_position} < {segment_length}; decide)"
            rest = append_lists([f"tuple{group}_{start // 16:03d} physical" for start in range(16 * (segment + 1), len(groups[group]), 16)] + ["[]"])
            member = f"List.mem_append_left (a := operand{i}.input.fields physical) (as := tuple{group}_{segment:03d} physical) ({rest}) ({member})"
            for previous in reversed(range(segment)):
                suffix = append_lists([f"tuple{group}_{later:03d} physical" for later in range(previous + 1, len(groups[group]) // 16 + (1 if len(groups[group]) % 16 else 0))] + ["[]"])
                member = f"List.mem_append_right (b := operand{i}.input.fields physical) (bs := {suffix}) (tuple{group}_{previous:03d} physical) ({member})"
            text += f"/-- Exact native matching supplies the public row for this primitive tuple. -/\ntheorem member{i} (physical : GKRAddress → F)\n    (arguments : NativeLookups.Arguments (circuitFor .{family}) (selectorsFor .{family}) physical (NativeWorkerSetup.rows .{family})) :\n    ∃ index, operand{i}.input.fields physical = NativeWorkerSetup.rows .{family} {group} index := by\n  kernel_exact native_member (family := .{family}) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := {group}) (values := operand{i}.input.fields physical) ({member})\n\n"
        outputs[directory / f"Members{start // 16:03d}.lean"] = text + ending
    return outputs


def cons_proof(terms):
    result = "(by intro value member; cases member)"
    for term in reversed(terms):
        result = f"(all_cons ({term}) {result})"
    return result


def append_proof(terms, segments):
    result = "(by intro value member; cases member)"
    for i in reversed(range(len(terms))):
        rest = append_lists(segments[i + 1:] + ["[]"])
        result = f"(all_append (first := {segments[i]}) (rest := {rest}) ({terms[i]}) {result})"
    return result


def emit_bridges(name):
    outputs = emit_family(name)
    circuit, native, source, logical, positions = load(name)
    family = LEAN_FAMILY[name]
    namespace = f"Proven.Compiler.WorkerConstraints.{name}"
    directory = ROOT / "proven/Proven/Compiler/WorkerConstraints" / name
    ending = f"\nend Airbender.Compiler.WorkerConstraints.{name}\n"
    by_group = {(row['group'], row['index']): row for row in source}
    comparisons = 0 if name in ("KeccakThetaRho", "KeccakChi5") else 2 * len(circuit['memory_layout']['ram_access_sets'])
    order = ([by_group[1, i] for i in range(len(circuit['range_check_16_lookup_expressions']))] +
             [by_group[2, i] for i in range(1 + comparisons, len(circuit['timestamp_range_check_lookup_expressions']))] +
             [by_group[0, i] for i in range(len(circuit['generic_lookups']))] +
             [by_group[2, i] for i in range(len(circuit['timestamp_range_check_lookup_expressions']))])
    chunk = 16
    query_parts = sorted({i // 12 for i in range(len(native))})
    field_parts = sorted({i // 8 for i in range(len(native))})
    text = lean_header(name, [f"{namespace}.Queries{i:03d}" for i in query_parts] +
                       ["Proven.Compiler.WorkerConstraints.Model"])
    groups = []
    for start in range(0, len(order), chunk):
        group = f"queries{start // chunk:03d}"
        groups.append(group)
        entries = ", ".join(f"sourceLookup{row['native']}" for row in order[start:start + chunk])
        text += f"/-- One complete segment of the imported description lookups. -/\nnoncomputable def {group} : List (Lookup F) := [{entries}]\n\n"
    text += "/-- Every imported lookup, including repeated alignment queries, in source order. -/\nnoncomputable def sourceQueries : List (Lookup F) :=\n  " + append_lists(groups + ["[]"]) + "\n\n"
    text += f"/-- The checked query list is exactly the full imported worker lookup list. -/\ntheorem source_binding : FlatOperation.lookups (constraints .{family}) = sourceQueries := by kernel_rfl\n\n"
    outputs[directory / "Source.lean"] = text + ending
    forward_parts = []
    for start in range(0, len(order), chunk):
        part = f"Lookups{start // chunk:03d}"
        forward_parts.append(f"{namespace}.{part}")
        rows = order[start:start + chunk]
        needed = sorted({row['native'] // 8 for row in rows})
        text = lean_header(name, [f"{namespace}.Source"] +
                           [f"{namespace}.Members{i:03d}" for i in sorted({row['native'] // 16 for row in rows})] +
                           [f"{namespace}.Fields{i:03d}" for i in needed])
        text += f"/-- Exact native matching supplies every lookup in this source segment. -/\ntheorem lookups{start // chunk:03d} (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (arguments : NativeLookups.Arguments (circuitFor .{family}) (selectorsFor .{family}) physical (NativeWorkerSetup.rows .{family})) :\n    ∀ query ∈ queries{start // chunk:03d}, query.Contains (Verification.environment logical) :=\n  "
        terms = [f"(refinement{row['native']} physical logical agreement).mpr (member{row['native']} physical arguments)" for row in rows]
        text += cons_proof(terms) + "\n"
        outputs[directory / f"{part}.lean"] = text + ending
    groups_native = [[i for i, row in enumerate(native) if row['group'] == group] for group in range(3)]
    backward_parts = []
    backward_names = [[], [], []]
    for group, indices in enumerate(groups_native):
        for start in range(0, len(indices), chunk):
            part = f"Converse{group}_{start // chunk:03d}"
            backward_parts.append(f"{namespace}.{part}")
            name_holds = f"converse{group}_{start // chunk:03d}"
            backward_names[group].append(name_holds)
            items = indices[start:start + chunk]
            needed = sorted({i // 8 for i in items})
            text = lean_header(name, [f"{namespace}.Source", f"{namespace}.Tuples"] + [f"{namespace}.Fields{i:03d}" for i in needed])
            for i in items:
                source_key = source[native[i]['source']]['key']
                position = next(j for j, row in enumerate(order) if row['key'] == source_key)
                text += f"/-- Accepted description lookups supply the native tuple at its actual placement. -/\ntheorem backwards{i} (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .{family})) :\n    ∃ index, operand{i}.input.fields physical = NativeWorkerSetup.rows .{family} {group} index := by\n  apply (refinement{i} physical logical agreement).mp\n  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2\n  rw [source_binding]\n  exact List.getElem_mem (l := sourceQueries) (n := {position}) (by change {position} < {len(order)}; decide)\n\n"
            entries = ", ".join(f"operand{i}.input.fields physical" for i in items)
            text += f"/-- Each tuple in this native segment has an interpreted public row. -/\ntheorem {name_holds} (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .{family})) :\n    ∀ values ∈ tuple{group}_{start // chunk:03d} physical, ∃ index, values = NativeWorkerSetup.rows .{family} {group} index :=\n  "
            text += cons_proof([f"backwards{i} physical logical agreement holds" for i in items]) + "\n"
            outputs[directory / f"{part}.lean"] = text + ending
    # Each source segment and native segment is checked independently before assembly.
    text = lean_header(name, forward_parts + backward_parts + ["Mathlib.Tactic.FinCases", "Proven.KernelExact"])
    text += f"/-- All description queries follow from the actual native lookup argument. -/\ntheorem lookups (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (arguments : NativeLookups.Arguments (circuitFor .{family}) (selectorsFor .{family}) physical (NativeWorkerSetup.rows .{family})) :\n    ∀ query ∈ FlatOperation.lookups (constraints .{family}), query.Contains (Verification.environment logical) := by\n  rw [source_binding]\n  kernel_exact "
    text += append_proof([f"lookups{i:03d} physical logical agreement arguments" for i in range(len(groups))], groups) + "\n\n"
    text += f"/-- Complete accepted source queries supply every actual native request. -/\ntheorem tuples_membership (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .{family})) :\n    ∀ group values, values ∈ tuples physical group → ∃ index, values = NativeWorkerSetup.rows .{family} group index := by\n  intro group\n  fin_cases group\n"
    for group in range(3):
        terms = [f"{item} physical logical agreement holds" for item in backward_names[group]]
        # The literal selector order is the concatenation of these checked segments.
        segments = [f"tuple{group}_{start // chunk:03d} physical" for start in range(0, len(groups_native[group]), chunk)]
        if terms:
            text += "  · kernel_exact " + append_proof(terms, segments) + "\n"
        else:
            text += "  · intro values member\n    change values ∈ ([] : List (List F)) at member\n    cases member\n"
    text += f"\n/-- Source lookup acceptance and actual placement construct the full native matching argument. -/\nnoncomputable def arguments_of_description (physical : GKRAddress → F) (logical : Nat → F)\n    (agreement : PlacementAgreement (Captures.{name}.imported.circuit) physical logical)\n    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .{family})) :\n    NativeLookups.Arguments (circuitFor .{family}) (selectorsFor .{family}) physical (NativeWorkerSetup.rows .{family}) :=\n  native_arguments (family := .{family}) (physical := physical) (tuples physical) (binding physical) (tuples_membership physical logical agreement holds)\n"
    outputs[directory.with_suffix('.lean')] = text + ending
    return outputs


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--family", action="append", choices=list(WORKERS))
    args = parser.parse_args()
    families = args.family or list(WORKERS)
    expected = {}
    for name in families:
        expected.update(emit_bridges(name))
    failures = []
    for path, text in expected.items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.is_file() or path.read_text() != text:
                path.write_text(text)
        elif not path.is_file() or path.read_text() != text:
            failures.append(str(path.relative_to(ROOT)))
    for name in families:
        directory = ROOT / "proven/Proven/Compiler/WorkerConstraints" / name
        actual = set(directory.glob("*.lean")) if directory.exists() else set()
        extra = actual - set(expected)
        if extra:
            failures.extend(str(path.relative_to(ROOT)) for path in sorted(extra))
    if failures:
        raise SystemExit("Worker constraint bindings differ: " + ", ".join(failures))
    print(f"PASS worker constraint bindings: {len(families)} circuits, {len(expected)} modules")


if __name__ == "__main__":
    main()
