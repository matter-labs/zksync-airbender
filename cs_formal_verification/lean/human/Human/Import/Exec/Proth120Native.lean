module
public import Human.Compiler.NativeLookups
public meta import Human.Compiler.NativeLookups
public import Human.Import.TranscribeCommand
public meta import Human.Import.TranscribeCommand
public import Human.Import.Proth120
public meta import Human.Import.Proth120

@[expose] public section
namespace Airbender.Compiler.Proth120Native

abbrev Terms := List (Nat × List GKRAddress)
/-- A sparse native gate: optional output and input terms with raw Montgomery coefficients and physical wires. -/
abbrev Gate := Option GKRAddress × Terms

/-- One primitive lookup leaf, including the native output chain's group, optional enable wire,
    and every physical field before compression. -/
structure Query where
  group : Nat
  enable : Option GKRAddress
  fields : List Terms
  deriving Repr

def value {F : Type} [CommRing F] (decode : Nat → F) (physical : GKRAddress → F) (terms : Terms) : F :=
  (terms.map fun (raw, wires) => decode raw * (wires.map physical).prod).sum

def Gate.Holds {F : Type} [CommRing F] (decode : Nat → F) (physical : GKRAddress → F)
    (gate : Gate) : Prop :=
  (gate.1.map physical).getD 0 =
    value decode physical gate.2

end Airbender.Compiler.Proth120Native

public meta section
namespace Airbender.Compiler.Proth120Native
open Lean Elab Command

open Airbender.UnifiedReduced.Proth120

deriving instance ToExpr for Query

def lookupFields (v : Json.Value) : Except String Terms := do
  let c : BoundedNat proth120Modulus ← fieldAs v "constant"
  let ts : List (BoundedNat proth120Modulus × GKRAddress) ← fieldAs v "linear_terms"
  return (c.val, []) :: ts.map fun (s, a) => (s.val, [a])

def quadratic? (gate : Json.Value) : Except String (Option Gate) := do
  let .obj [(tag, data)] ← jsonMember gate "enforced_relation" | throw "invalid GKR relation"
  unless tag == "MaxQuadratic" || tag == "EnforceSingleMaxQuadraticConstraint" do return none
  let out ← if tag == "MaxQuadratic" then some <$> fieldAs data "output" else pure none
  let input ← jsonMember data "input"
  let q : List (GKRAddress × List (BoundedNat proth120Modulus × GKRAddress)) ← fieldAs input "quadratic_terms"
  return some (out, (← lookupFields input) ++ q.flatMap fun (a, terms) =>
    terms.map fun (s, b) => (s.val, [a, b]))

abbrev Definition := GKRAddress × Sum GKRAddress (List Terms)

def cacheDefinition (v : Json.Value) : Except String (Option Definition) := do
  let .arr [a, .obj [(tag, d)]] := v | throw "malformed cache"
  let addr ← Decode.decode a
  match tag with
  | "SingleColumnLookup" =>
    let fields ← lookupFields (← jsonMember (← jsonMember d "relation") "input")
    return some (addr, .inr [fields])
  | "VectorizedLookup" => return some (addr, .inr (← (← jsonArray (← jsonMember d "columns")).mapM lookupFields))
  | "MemoryTuple" | "VectorizedLookupSetup" => return none
  | _ => throw s!"unsupported native cache {tag}"

def expand (defs : List Definition) : Nat → GKRAddress → Except String (List Terms)
  | 0, _ => throw "cyclic materialization chain"
  | n+1, address => match defs.lookup address with
    | some (.inl a) => expand defs n a
    | some (.inr fields) => return fields
    | none => match address with
      | .BaseLayerMemory _ | .BaseLayerWitness _ | .InnerLayer .. =>
        return [[(2 ^ 128 % proth120Modulus, [address])]]
      | _ => throw "unresolved lookup operand"

/-- Use the common native rational-chain semantics to identify each leaf's setup group.
    Expand scalar/vector caches and copy gates to the physical inputs of that primitive.
    Quadratic gates do not contribute lookup leaves, rational links or copies. -/
def queryProjection (json : Json.Value) (layers : List Json.Value) : Except String (List Query) := do
  let mut state : NativeLookups.ChainStore := ∅
  let mut leaves := #[]
  let mut defs : List Definition := []
  let mut i := 0
  for layer in layers do
    for v in ← jsonArray (← jsonMember layer "cached_relations") do
      if let some binding ← cacheDefinition v then defs := binding :: defs
    for g in (← jsonArray (← jsonMember layer "gates")) ++
        (← jsonArray (← jsonMember layer "gates_with_external_connections")) do
      let .obj [(tag, _)] ← jsonMember g "enforced_relation" | throw "malformed native gate"
      if tag != "MaxQuadratic" && tag != "EnforceSingleMaxQuadraticConstraint" then
        let gate : GateArtifacts ← Decode.decode g
        state ← NativeLookups.chainStep state (gate, i)
        match gate.enforced_relation with
        | .CopyInBaseField a b | .CopyInExtensionField a b => defs := (b, .inl a) :: defs
        | _ => pure ()
        for (operand, j) in (← NativeLookups.operands gate.enforced_relation).toList.zipIdx do
          unless operand.weight.isTable do
            let .address addr := operand.input | throw "unsupported direct lookup input"
            let mask ← match operand.weight with
              | .one => pure none | .column a => pure (some a) | _ => throw "invalid query weight"
            leaves := leaves.push ((i, j), mask, addr)
      i := i+1
  let outputs : ObjectMap OutputType (Array GKRAddress) ← fieldAs json "global_output_map"
  let groups ← outputs.entries.toList.flatMapM fun (tag, wires) => do
    let some group := NativeLookups.outputGroup tag | return []
    return (← NativeLookups.readChain state wires.toList).map fun pos => (pos, group.val)
  leaves.toList.mapM fun (pos, mask, addr) => do
    let [(_, group)] := groups.filter (fun kv => kv.1 == pos) | throw "lookup leaf has no unique output chain"
    return ⟨group, mask, ← expand defs (defs.length+1) addr⟩

/-- Read the exact physical placements and every sparse quadratic gate of the cached layers. -/
elab "import_proth120_native " gates:ident placements:ident queries:ident " from " path:str : command => do
  let src ← IO.FS.readFile path.getString
  let data : Except String (List Gate × List (Nat × GKRAddress) × List Query) := do
    let json ← Json.parse src.toUTF8
    let placement : ObjectMap Nat GKRAddress ← fieldAs json "placement_data"
    let layers ← jsonArray (← jsonMember json "layers")
    let all ← layers.mapM fun layer => do
      let gs ← jsonArray (← jsonMember layer "gates")
      let ext ← jsonArray (← jsonMember layer "gates_with_external_connections")
      return (← (gs ++ ext).mapM quadratic?).reduceOption
    return (all.flatten, placement.entries.toList, ← queryProjection json layers)
  let (gs, ps, qs) ← match data with
    | .ok result => pure result
    | .error msg => throwError "cannot read native arithmetic: {msg}"
  let ns ← getCurrNamespace
  liftCoreM do
    addTranscribedDef (ns ++ gates.getId) (toTypeExpr (List Gate)) (toExpr gs)
    addTranscribedDef (ns ++ queries.getId) (toTypeExpr (List Query)) (toExpr qs)
    addTranscribedDef (ns ++ placements.getId) (toTypeExpr (List (Nat × GKRAddress))) (toExpr ps)

end Airbender.Compiler.Proth120Native
