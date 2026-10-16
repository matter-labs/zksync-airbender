import Airbender.Import.SetupEmbed
import Lean.Util.ReplaceExpr
import Lean.AddDecl

namespace Airbender.Setup
open Lean Elab Command

private partial def literalArray (values : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  if values.size ≤ 64 then return ← `(#[$[$values],*])
  let left ← literalArray (values.extract 0 (values.size / 2))
  let right ← literalArray (values.extract (values.size / 2) values.size)
  `(Array.append $left $right)

/-- Import stored periodic templates at exact native region-relative offsets.
    These are parsed values; neither a recipe nor expanded lookup rows is emitted. -/
elab "import_setup_templates " name:ident " from " path:str
    " native_table_id " id:num " physical_column " column:num
    " row_offsets " "[" offsets:num,* "]" : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let some physical := artifact.columns[column.getNat]?
    | throwError "setup template column is absent"
  let offsets := offsets.getElems.map (·.getNat)
  let mut repetitions : Array Nat := #[]
  let mut strides : Array Int := #[]
  for i in [:offsets.size] do
    let row := offsets[i]!
    unless row < region.length do throwError "setup template offset is outside its native region"
    let target := region.offset + row
    let mut position := 0
    let mut selected : Option Block := none
    for block in physical.blocks do
      if position == target then selected := some block
      position := position + block.length
    let some block := selected
      | throwError "setup template offset is not a stored block boundary"
    unless row + block.length ≤ region.length do
      throwError "setup template block crosses its native region"
    let .periodic count stride values := block
      | throwError "setup template block is not periodic"
    let term ← literalArray (values.map quote)
    let valueName := mkIdent (name.getId.appendAfter (toString i))
    elabCommand (← `(def $valueName : Array Nat := $term))
    repetitions := repetitions.push count
    strides := strides.push stride
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  let regionName := mkIdent (name.getId.appendAfter "Region")
  let columnName := mkIdent (name.getId.appendAfter "Column")
  let offsetsName := mkIdent (name.getId.appendAfter "RowOffsets")
  let countsName := mkIdent (name.getId.appendAfter "Repetitions")
  let stridesName := mkIdent (name.getId.appendAfter "Strides")
  let strideTerms ← strides.mapM fun stride => do
    if stride ≥ 0 then `(Int.ofNat $(quote stride.toNat))
    else `(Int.negSucc $(quote (-stride - 1).toNat))
  elabCommand (← `(def $sourceName : String := $(quote source)))
  elabCommand (← `(def $regionName : Airbender.Setup.Region :=
    Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns)))
  elabCommand (← `(def $columnName : Nat := $(quote column.getNat)))
  elabCommand (← `(def $offsetsName : Array Nat := $(quote offsets)))
  elabCommand (← `(def $countsName : Array Nat := $(quote repetitions)))
  elabCommand (← `(def $stridesName : Array Int := #[$[$strideTerms],*]))

/-- Share exact imported literal subexpressions through their existing definitions.
    Alpha-equality is checked before each substitution; no table formula is used. -/
elab "share_setup_literals " name:ident " from " original:ident
    " using " "[" templates:ident,* "]" : command => do
  let currentNamespace ← getCurrNamespace
  let originalName ← resolveGlobalConstNoOverload original
  let info ← getConstInfoDefn originalName
  unless info.type.getAppFn.isConstOf ``TableData do
    throwError "literal sharing requires imported setup TableData"
  let mut value := info.value
  for template in templates.getElems do
    let templateName ← resolveGlobalConstNoOverload template
    let templateInfo ← getConstInfoDefn templateName
    unless templateInfo.type == mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat) do
      throwError "shared setup literal must be an Array Nat definition"
    let next := value.replace fun expression =>
      if expression == templateInfo.value then some (mkConst templateName) else none
    if next == value then throwError "shared setup literal {templateName} is absent from imported data"
    value := next
  let fullName := currentNamespace ++ name.getId
  let height := getMaxHeight (← getEnv) value + 1
  liftCoreM <| addAndCompile (.defnDecl {
    name := fullName, levelParams := info.levelParams, type := info.type,
    value, hints := .regular height, safety := .safe })
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  let regionName := mkIdent (name.getId.appendAfter "Region")
  let originalSource := mkIdent (originalName.appendAfter "SourceBytes")
  let originalRegion := mkIdent (originalName.appendAfter "Region")
  elabCommand (← `(def $sourceName : String := $originalSource))
  elabCommand (← `(def $regionName : Airbender.Setup.Region := $originalRegion))

end Airbender.Setup
