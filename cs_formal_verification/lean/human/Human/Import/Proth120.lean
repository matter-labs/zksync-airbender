module
public import Human.Helpers.Core.CircuitField
public import Human.Import.Exec.Decode
public import Human.Import.Operations

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

abbrev montgomeryInverse := CircuitField.montgomeryInverse proth120Modulus
abbrev signedScalar (raw : BoundedNat proth120Modulus) := CircuitField.signedScalar proth120Modulus raw.val

def jsonMember (v : Json.Value) (key : String) : Except String Json.Value := do
  let .obj fields := v | throw s!"expected object containing {key}"
  let some value := fields.lookup key | throw s!"missing {key}"
  return value

def jsonArray : Json.Value → Except String (List Json.Value)
  | .arr xs => .ok xs
  | _ => .error "expected an array"

def fieldAs [Decode α] (obj : Json.Value) (key : String) : Except String α := do
  Decode.decode (← jsonMember obj key)

mutual
/-- Structured `Sum` and `Product` retain the fold order used by `Import.expression`. -/
def expr : Json.Value → Except String (Expression Int)
  | .obj [(tag, x)] => do
    match tag with
    | "Var" => return .var ⟨← Decode.decode x⟩
    | "Constant" => return .const (signedScalar (← Decode.decode x))
    | "Sum" => return (← exprItems x).foldl .add (.const 0)
    | "Product" => return (← exprItems x).foldl .mul (.const 1)
    | _ => throw "unknown structured expression"
  | _ => .error "invalid structured expression"
def exprItems : Json.Value → Except String (List (Expression Int))
  | .arr xs => exprList xs
  | _ => .error "expected expression array"
def exprList : List Json.Value → Except String (List (Expression Int))
  | [] => .ok []
  | x :: xs => do return (← expr x) :: (← exprList xs)
end

def statement (v : Json.Value) : Except String (Expression Int) := do
  let .obj [(tag, data)] := v | throw "invalid structured statement"
  let e ← jsonMember data "expr"
  let rhs ← expr e
  match tag with
  | "AssertZero" => return rhs
  | "Define" => return .add (.var ⟨← fieldAs data "dst"⟩) (.mul (.const (-1)) rhs)
  | _ => throw s!"unsupported statement {tag}"

/-- Resolve native affine queries through the same checked placement and scratch aliases as BabyBear. -/
def affine (c : Circuit) (v : Json.Value) : Except String (Expression Int) := do
  let terms : List (BoundedNat proth120Modulus × GKRAddress) ← fieldAs v "linear_terms"
  let constant := signedScalar (← fieldAs v "constant")
  let mut e : Expression Int := .add (.const 0) (.const constant)
  for (raw, address) in terms do
    let var := ← c.logicalVariable address
    e := .add e (.mul (.mul (.const 1) (.const (signedScalar raw))) (.var ⟨var⟩))
  return e

/-- The four source sections supplying the unified logical row, retained before any coefficient
    decoding, expression translation, or physical-to-logical column resolution. -/
structure RowSource where
  statements : List Json.Value
  ranges : List Json.Value
  pooled : List Json.Value
  clocks : List Json.Value

def RowSource.read (json : Json.Value) : Except String RowSource := do
  let sectionOf (key : String) := do jsonArray (← jsonMember json key)
  return ⟨← sectionOf "structured_statements", ← sectionOf "range_check_16_lookup_expressions",
    ← sectionOf "generic_lookups", ← sectionOf "timestamp_range_check_lookup_expressions"⟩

def RowSource.scalars (xs : List Json.Value) (c : Circuit) : Except String (List (Expression Int)) :=
  xs.mapIdxM fun i q => do
    unless (← fieldAs q "lookup_set_index") == i do throw "range lookup index mismatch"
    affine c (← jsonMember q "input")

def RowSource.tables (src : RowSource) (c : Circuit) : Except String (List (Vector (Expression Int) 10)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 10 && c.has_decoder_lookup &&
      c.num_generic_lookups == 6 && src.pooled.length == 5 do throw "unexpected unified lookup profile"
  src.pooled.mapIdxM fun i q => do
    let xs := (← (← jsonArray (← jsonMember q "columns")).mapM (affine c)).toArray
    unless (← fieldAs q "lookup_set_index") == i do throw "invalid pooled lookup index"
    if h : xs.size = 10 then return ⟨xs, h⟩ else throw "invalid pooled lookup width"

def castExpr {p : Nat} : Expression Int → Expression (ZMod p)
  | .var v => .var ⟨v.index⟩
  | .const n => .const (Int.cast n)
  | .add a b => .add (castExpr a) (castExpr b)
  | .mul a b => .mul (castExpr a) (castExpr b)

/-- The asserted polynomials and the fifteen range, five pooled and eight clock queries,
    interpreted directly from the respective serialized row sections. -/
def RowSource.operations {p : Nat} [Fact p.Prime] (r : RowSource) (c : Circuit)
    (setup : Table (ZMod p) (fields 10)) :
    Except String (List (FlatOperation (ZMod p)) × List (FlatOperation (ZMod p))) := do
  let eqs ← r.statements.mapM statement
  let small ← scalars r.ranges c
  let fixed ← r.tables c
  let clocks ← scalars r.clocks c
  return (eqs.map (fun e => .assert (castExpr e)) ++
    small.map (fun e => .lookup (Verification.range16 (castExpr e))) ++
    fixed.map (fun v => .lookup ⟨setup.toRaw, v.map castExpr⟩),
    clocks.map (fun e => .lookup (Trace.timestampLookup (castExpr e))))

end Airbender.UnifiedReduced.Proth120
