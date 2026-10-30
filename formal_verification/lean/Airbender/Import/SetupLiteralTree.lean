import Airbender.Import.SetupEmbed

namespace Airbender.Setup.LiteralTree
open Lean Elab Command
set_option warningAsError true

/-- Shared literal nodes. Fuel separates branch indices from final native values. -/
structure Column where
  depth : Nat
  root : Nat
  nodes : Array (Vector Nat 16)
  deriving Repr

def Column.entry (column : Column) (node digit : Nat) : Nat :=
  match column.nodes[node]? with
  | none => 0
  | some values => values[digit % 16]'(Nat.mod_lt _ (by decide))

def Column.evaluate (column : Column) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | remaining + 1, node, row =>
    let value := column.entry node (row / 16 ^ remaining % 16)
    if remaining = 0 then value else column.evaluate remaining value row

def Column.value (column : Column) (row : Nat) : Nat :=
  column.evaluate column.depth column.root row

/-- Complete physical rows of one retained native region. -/
structure Region (width : Nat) where
  length : Nat
  columns : Vector Column width
  deriving Repr

def Region.row (region : Region width) (index : Fin region.length) : Vector Nat width :=
  region.columns.map (fun column => column.value index.val)

def Region.table {p : Nat} [Fact p.Prime] (name : String) (region : Region width) :
    Table (ZMod p) (fields width) := .fromStatic {
  name := name
  length := region.length
  row index := (region.row index).map (fun value : Nat => (signedValue value : ZMod p))
  index _ := 0
  Spec entry := ∃ index : Fin region.length,
    entry = (region.row index).map (fun value : Nat => (signedValue value : ZMod p))
  contains_iff _ := Iff.rfl
}

private def selectedValues (column : Airbender.Setup.Column) (offset length : Nat) : Except String (Array Nat) := do
  let mut position := 0
  let mut values := Array.mkEmpty length
  for block in column.blocks do
    let first := max offset position
    let last := min (offset + length) (position + block.length)
    if first < last then
      for index in [first - position:last - position] do
        let some value := block.get? index | throw "absent native setup value"
        values := values.push value
    position := position + block.length
  unless values.size = length do throw "native literal region length mismatch"
  return values

private def makeColumn (depth : Nat) (values : Array Nat) : Except String Column := do
  unless 0 < depth && values.size ≤ 16 ^ depth do throw "native literal tree capacity is invalid"
  let mut nodes : Array (Vector Nat 16) := #[]
  let mut intern : Std.HashMap (Array Nat) Nat := {}
  let mut layer := values ++ Array.replicate (16 ^ depth - values.size) 0
  for _ in [:depth] do
    unless layer.size % 16 = 0 do throw "native literal level is not divisible by sixteen"
    let mut parents := Array.mkEmpty (layer.size / 16)
    for group in [:layer.size / 16] do
      let digits := layer.extract (16 * group) (16 * group + 16)
      let id ← match intern[digits]? with
        | some id => pure id
        | none => do
          let id := nodes.size
          let node : Vector Nat 16 ← if bound : digits.size = 16 then pure ⟨digits, bound⟩
            else throw "native literal node has an incomplete row"
          nodes := nodes.push node
          intern := intern.insert digits id
          pure id
      parents := parents.push id
    layer := parents
  unless layer.size = 1 do throw "native literal region has no unique root"
  let column : Column := ⟨depth, layer[0]!, nodes⟩
  for row in [:values.size] do
    unless column.value row = values[row]! do throw "native literal tree changed a source value"
  return column

private def columnSyntax (column : Column) : CommandElabM (TSyntax `term) := do
  let nodes ← column.nodes.mapM fun node => do
    let values := node.toArray.map quote
    `(#v[$[$values],*])
  `(Airbender.Setup.LiteralTree.Column.mk $(quote column.depth) $(quote column.root) #[$[$nodes],*])

/-- Import a complete native region as shared literal nodes. Compare every physical value. -/
elab "import_setup_literal_tree " name:ident " from " path:str " native_table_id " id:num : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "native literal import failed: {error}"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "native literal table ID is absent"
  let mut extent := 16
  let mut depth := 1
  while extent < region.length do
    extent := 16 * extent
    depth := depth + 1
  unless 0 < region.length do
    throwError "native literal region must contain a row"
  let columns ← artifact.columns.mapIdxM fun index column => do
    let values ← match selectedValues column region.offset region.length with
      | .ok values => pure values
      | .error error => throwError "native literal selection failed: {error}"
    let encoded ← match makeColumn depth values with
      | .ok encoded => pure encoded
      | .error error => throwError "native literal encoding failed: {error}"
    logInfo m!"native literal column {index}: {encoded.nodes.size} shared nodes; all {values.size} values checked"
    let encodedTerm ← columnSyntax encoded
    if region.length = extent then return encodedTerm
    let columnName := mkIdent (name.getId.appendAfter s!"Column{index}")
    elabCommand (← `(private def $columnName : Airbender.Setup.LiteralTree.Column := $encodedTerm))
    `($columnName)
  elabCommand (← `(def $name : Airbender.Setup.LiteralTree.Region $(quote columns.size) :=
    Airbender.Setup.LiteralTree.Region.mk $(quote region.length) #v[$[$columns],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let regionName := mkIdent (name.getId.appendAfter "Region")
  elabCommand (← `(def $regionName : Airbender.Setup.Region :=
    Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns)))

end Airbender.Setup.LiteralTree
