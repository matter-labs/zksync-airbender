import Airbender.Import.Schema

namespace Airbender
open Lean

namespace StrictJson
open Std.Internal.Parsec Std.Internal.Parsec.String

/- Reuse Lean's primitive JSON parsers; reject duplicate keys at every object depth. -/
mutual
  partial def value : Parser Json := do
    let c ← peek!
    if c == '{' then
      skip; ws
      if (← peek!) == '}' then
        skip; ws
        return .obj {}
      else
        return .obj (← object {})
    else if c == '[' then
      skip; ws
      if (← peek!) == ']' then
        skip; ws
        return .arr #[]
      else
        return .arr (← array #[])
    else
      Json.Parser.anyCore

  partial def object (acc : Std.TreeMap.Raw String Json) :
      Parser (Std.TreeMap.Raw String Json) := do
    if (← any) != '"' then fail "expected object key"
    let key ← Json.Parser.str
    if acc.contains key then fail s!"duplicate object key: {key}"
    ws
    if (← any) != ':' then fail "expected colon"
    ws
    let v ← value
    let next ← any
    if next == '}' then
      ws
      return acc.insert key v
    else if next == ',' then
      ws
      object (acc.insert key v)
    else
      fail "expected comma or closing brace"

  partial def array (acc : Array Json) : Parser (Array Json) := do
    let v ← value
    let next ← any
    if next == ']' then
      ws
      return acc.push v
    else if next == ',' then
      ws
      array (acc.push v)
    else
      fail "expected comma or closing bracket"
end

def parse (s : String) : Except String Json :=
  (do ws; let j ← value; eof; return j).run s

end StrictJson

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

/-- Check storage bounds and require every cache reference to have a definition.
    This is a structural check, not a proof of circuit soundness. -/
def Circuit.checkAddress (c : Circuit) (a : GKRAddress) : Except String Unit := do
  match a with
  | .BaseLayerWitness i => require (i < c.witness_layout.total_width) "witness address out of bounds"
  | .BaseLayerMemory i => require (i < c.memory_layout.total_width) "memory address out of bounds"
  | .Setup i => require (i < c.generic_lookup_tables_width) "setup address out of bounds"
  | .ScratchSpace i => require (i < c.scratch_space_size) "scratch address out of bounds"
  | .VirtualSetup _ => pure ()
  | .InnerLayer layer offset =>
    if layer == c.layers.size then
      let some last := c.layers.back? | throw "circuit has no layers"
      let addressJson := toJson a
      let produced := (last.gates ++ last.gates_with_external_connections).any fun g =>
        let relationFields := (toJson g.enforced_relation).getObj?.toOption.map (·.toArray)
        match relationFields with
        | some fields => fields.any fun (_, payload) =>
          match (payload.getObjVal? "output").toOption with
          | some output => output == addressJson ||
              ((output.getArr?).toOption.getD #[]).contains addressJson
          | none => false
        | none => false
      require produced "terminal address is not produced by a final gate"
      return
    let some l := c.layers[layer]? | throw "inner address names a nonexistent layer"
    let some width := l.intermediate_layer_width | throw "inner address names the base layer"
    require (offset < width) "inner address out of bounds"
  | .Cached layer offset =>
    let some l := c.layers[layer]? | throw "cache address names a nonexistent layer"
    require (l.cached_relations.any fun (key, _) => toJson key == toJson (.Cached layer offset : GKRAddress))
      "cache address has no definition"

/-- Walk the typed object's JSON encoding, checking all explicitly tagged addresses.
    Untagged RAM offsets are preserved but are not covered by this check. -/
private partial def checkEncodedTree (c : Circuit) (j : Json) : Except String Unit := do
  match j with
  | .num _ =>
    let n ← j.getNat?
    require (n < 18446744073709551616) "integer exceeds the v3 64-bit index profile"
  | .arr xs => xs.forM (checkEncodedTree c)
  | .obj fields =>
    let entries := fields.toArray
    if entries.size == 1 then
      let tag := entries[0]!.1
      if #["BaseLayerWitness", "BaseLayerMemory", "InnerLayer", "Setup", "VirtualSetup",
          "ScratchSpace", "Cached"].contains tag then
        let address : GKRAddress ← fromJson? j
        c.checkAddress address
    entries.forM fun (_, v) => checkEncodedTree c v
  | _ => pure ()

def Circuit.validate (c : Circuit) : Except String Unit := do
  require (c.trace_len > 0 && c.trace_len &&& (c.trace_len - 1) == 0)
    "trace length must be a nonzero power of two"
  require (!c.layers.isEmpty) "circuit has no layers"
  for i in [:c.layers.size] do
    let some l := c.layers[i]? | throw "missing layer"
    require (l.layer == i) "layer numbers must equal their array positions"
    require ((i == 0) == l.intermediate_layer_width.isNone) "invalid intermediate layer width"
    for g in l.gates ++ l.gates_with_external_connections do
      require (g.output_layer == i + 1 && g.output_layer ≤ c.layers.size)
        "gate output layer is inconsistent with its containing layer"
    let mut keys : Array Json := #[]
    for (key, _) in l.cached_relations do
      match key with
      | .Cached layer _ => require (layer == i) "cache definition is in the wrong layer"
      | _ => throw "cache definition requires a Cached address"
      require (!(keys.contains (toJson key))) "duplicate cache definition"
      keys := keys.push (toJson key)
  for r in #[c.witness_layout.multiplicities_columns_for_range_check_16,
             c.witness_layout.multiplicities_columns_for_timestamp_range_check,
             c.witness_layout.multiplicities_columns_for_generic_lookup] do
    require (r.start ≤ r.end && r.end ≤ c.witness_layout.total_width) "invalid witness column range"
  for (v, _) in c.placement_data.entries do
    require (v < 18446744073709551616) "variable index exceeds 64 bits"
  for (v, _) in c.variable_names.entries do
    require (v < 18446744073709551616) "variable name index exceeds 64 bits"
  let hasVariable := fun v => c.placement_data.entries.any fun (key, _) => key == v
  for r in c.degree_1_constraints do
    for (_, v) in r.linear_terms do require (hasVariable v) "unplaced variable in degree-one constraint"
  for r in c.degree_2_constraints do
    for (_, v) in r.linear_terms do require (hasVariable v) "unplaced variable in degree-two constraint"
    for t in r.quadratic_terms do
      require (hasVariable t.second && hasVariable t.third) "unplaced variable in quadratic term"
  for statement in c.structured_statements do
    let constraint := match statement with
      | .AssertZero _ constraint _ => constraint
      | .Define _ constraint _ _ => constraint
    for t in constraint.terms do
      if let .Expression _ inner degree := t then
        require (degree ≤ 4) "term degree exceeds the serialized capacity"
        for i in [:4] do
          if i < degree then
            require (hasVariable inner.values[i]!) "unplaced variable in retained term"
          else
            require (inner.values[i]! == 18446744073709551615) "invalid term placeholder"
  checkEncodedTree c (toJson c)

/-- Strict schema decoding: unknown fields/variants and lossy decoding are rejected.
    Numeric object keys are canonical decimal strings; integer sentinels remain exact. -/
def decodeCircuitJson (j : Json) : Except String Circuit := do
  let c : Circuit ← fromJson? j
  require (toJson c == j) "JSON does not exactly match the pinned v3 circuit schema"
  c.validate
  return c

def parseCircuit (text : String) : Except String Circuit := do
  decodeCircuitJson (← StrictJson.parse text)

def loadCircuit (path : System.FilePath) : IO (Except String Circuit) := do
  return parseCircuit (← IO.FS.readFile path)

end Airbender
