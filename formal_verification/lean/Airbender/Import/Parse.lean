import Airbender.Import.Schema

namespace Airbender
open Lean

def Circuit.logicalVariable (c : Circuit) (address : ColumnAddress) : Except String Nat := do
  let inBounds : Bool := match address with
    | .WitnessSubtree n => decide (n < c.witness_layout.total_width)
    | .MemorySubtree n => decide (n < c.memory_layout.total_width)
    | .SetupSubtree n => decide (n < c.setup_layout.total_width)
  unless inBounds do throw "physical column outside native layout"
  match (c.variable_mapping.entries.filter fun (_, a) => a == address).toList with
  | [(v, _)] => pure v
  | _ => throw "physical column must have exactly one logical variable"

def Circuit.linearExpression (c : Circuit) (relation : CompiledDegree1Constraint) :
    Except String Expr := do
  let terms ← relation.linear_terms.mapM fun (a, v) => do
    pure (.Product #[.Constant a, .Var (← c.logicalVariable v)] : Expr)
  pure (.Sum (#[.Constant relation.constant_term] ++ terms))

def Circuit.quadraticExpression (c : Circuit) (relation : CompiledDegree2Constraint) :
    Except String Expr := do
  let terms ← relation.quadratic_terms.mapM fun t => do
    pure (.Product #[.Constant t.first, .Var (← c.logicalVariable t.second),
      .Var (← c.logicalVariable t.third)] : Expr)
  let linear ← c.linearExpression ⟨relation.linear_terms, relation.constant_term⟩
  pure (.Sum (#[linear] ++ terms))

def Circuit.lookupExpression (c : Circuit) : LookupExpression → Except String Expr
  | .Variable a => Expr.Var <$> c.logicalVariable a
  | .Expression e => c.linearExpression e

private def Circuit.hasBoolean (c : Circuit) (address : ColumnAddress) : Bool :=
  c.degree_2_constraints.any fun q =>
    match q.quadratic_terms.toList, q.linear_terms.toList with
    | [term], [(coefficient, column)] =>
      term.first.canonical == 1 && term.second == address && term.third == address &&
        coefficient.canonical == mersenne31Modulus - 1 && column == address &&
        q.constant_term.canonical == 0
    | _, _ => false

/-- Check every consumed address and expression before emitting a theorem target. -/
def Circuit.validate (c : Circuit) : Except String Unit := do
  let keys := c.variable_mapping.entries.map Prod.fst
  unless keys.toList.Nodup do throw "duplicate logical variable IDs"
  for (_, address) in c.variable_mapping.entries do
    let _ ← c.logicalVariable address
  let w := c.witness_layout
  unless w.boolean_vars_columns_range.start + w.boolean_vars_columns_range.num_elements ≤ w.total_width do
    throw "Boolean column range outside witness layout"
  unless w.range_check_8_columns.num_elements == 0 do
    throw "8-bit range columns are not yet supported"
  unless w.range_check_16_columns.start + w.range_check_16_columns.num_elements ≤ w.total_width do
    throw "16-bit column range outside witness layout"
  for i in [:w.boolean_vars_columns_range.num_elements] do
    unless c.hasBoolean (.WitnessSubtree (w.boolean_vars_columns_range.start + i)) do
      throw "native Boolean column lacks its polynomial constraint"
  for i in [:w.range_check_16_columns.num_elements] do
    let address := ColumnAddress.WitnessSubtree (w.range_check_16_columns.start + i)
    unless w.range_check_16_lookup_expressions.any (fun query => match query with
        | .Variable a => a == address
        | _ => false) do
      throw "native 16-bit column lacks its range query"
  for q in c.degree_2_constraints do
    let _ ← c.quadraticExpression q
  for q in c.degree_1_constraints do
    let _ ← c.linearExpression q
  for q in w.range_check_16_lookup_expressions ++ w.timestamp_range_check_lookup_expressions do
    let _ ← c.lookupExpression q

def parseCircuit (source : String) : Except String Circuit := do
  let json ← Json.parse source
  let c : Circuit ← fromJson? json
  c.validate
  pure c

def loadCircuit (path : System.FilePath) : IO (Except String Circuit) :=
  parseCircuit <$> IO.FS.readFile path

end Airbender
