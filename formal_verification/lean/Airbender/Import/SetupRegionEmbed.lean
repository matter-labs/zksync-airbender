import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Slices
open Lean Elab Command
set_option warningAsError true

private partial def arraySyntax (values : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  if values.size ≤ 64 then return ← `(#[$[$values],*])
  let left ← arraySyntax (values.extract 0 (values.size / 2))
  let right ← arraySyntax (values.extract (values.size / 2) values.size)
  `(Array.append $left $right)

/-- Compact literal data only after comparing every parsed element. These
    constructors do not select a table recipe or infer unexported values. -/
private def valuesSyntax (values : Array Nat) : CommandElabM (TSyntax `term) := do
  if let some first := values[0]? then
    if values.all (· == first) then
      return ← `(Array.replicate $(quote values.size) $(quote first))
    if (values.mapIdx fun i value => value == i).all id then
      return ← `(Array.range $(quote values.size))
    if (values.mapIdx fun i value => value == first + i).all id then
      return ← `(Array.ofFn (fun i : Fin $(quote values.size) => $(quote first) + i.val))
    if (values.mapIdx fun i value => value == (first + i) % values.size).all id then
      return ← `(Array.ofFn (fun i : Fin $(quote values.size) =>
        ($(quote first) + i.val) % $(quote values.size)))
    let run := (values.toList.takeWhile (· == first)).length
    if 1 < run && run < values.size then
      let some next := values[run]? | throwError "setup run encoding is out of bounds"
      if first ≤ next then
        let step := next - first
        if (values.mapIdx fun i value => value == first + step * (i / run)).all id then
          return ← `(Array.ofFn (fun i : Fin $(quote values.size) =>
            $(quote first) + $(quote step) * (i.val / $(quote run))))
    if 1 < run && run < values.size && values.size % run == 0 then
      let compact := (Array.range (values.size / run)).map fun i =>
        (values[i * run]?).getD 0
      if (values.mapIdx fun i value => value == (compact[i / run]?).getD 0).all id then
        let encoded ← arraySyntax (compact.map quote)
        return ← `(Array.ofFn (fun i : Fin $(quote values.size) =>
          ($encoded[i.val / $(quote run)]?).getD 0))
  let values := values.map quote
  arraySyntax values

private def blockSyntax (block : Block) : CommandElabM (TSyntax `term) := do
  match block with
  | .affine length first step =>
    let step ← if step ≥ 0 then `(Int.ofNat $(quote step.toNat))
      else `(Int.negSucc $(quote (-step - 1).toNat))
    `(Airbender.Setup.Block.affine $(quote length) $(quote first) $step)
  | .dense values =>
    let values ← valuesSyntax values
    `(Airbender.Setup.Block.dense $values)
  | .periodic repetitions stride values =>
    let stride ← if stride ≥ 0 then `(Int.ofNat $(quote stride.toNat))
      else `(Int.negSucc $(quote (-stride - 1).toNat))
    let values ← valuesSyntax values
    `(Airbender.Setup.Block.periodic $(quote repetitions) $stride $values)

private def columnSyntax (column : Column) : CommandElabM (TSyntax `term) := do
  let blocks ← column.blocks.mapM blockSyntax
  let blocks ← arraySyntax blocks
  `(({blocks := $blocks} : Airbender.Setup.Column))

private def sliceBlock (block : Block) (start count : Nat) : Array Block := Id.run do
  if start = 0 ∧ count = block.length then return #[block]
  match block with
  | .affine _ _ step => return #[.affine count ((block.get? start).getD 0) step]
  | .dense values => return #[.dense (values.extract start (start + count))]
  | .periodic _ stride values =>
    let leading := min count ((values.size - start % values.size) % values.size)
    let cycleCount := (count - leading) / values.size
    let trailing := (count - leading) % values.size
    let mut result := #[]
    if leading > 0 then
      result := result.push (.dense ((Array.range leading).map fun i =>
        (block.get? (start + i)).getD 0))
    if cycleCount > 0 then
      result := result.push (.periodic cycleCount stride
        ((Array.range values.size).map fun i => (block.get? (start + leading + i)).getD 0))
    if trailing > 0 then
      result := result.push (.dense ((Array.range trailing).map fun i =>
        (block.get? (start + leading + cycleCount * values.size + i)).getD 0))
    return result
private def sliceColumn (column : Column) (start count : Nat) : Column := Id.run do
  let mut position := 0
  let mut blocks := #[]
  for block in column.blocks do
    let first := max start position
    let last := min (start + count) (position + block.length)
    if first < last then blocks := blocks ++ sliceBlock block (first - position) (last - first)
    position := position + block.length
  return ⟨blocks⟩


/-- Compare every selected source value with its encoded slice, without
    materializing either column. Unsupported or missing cells fail closed. -/
def matchesSource (source sliced : Column) (offset length : Nat) : Bool := Id.run do
  let mut sourceBlock := 0
  let mut sourceRow := offset
  for _ in [:source.blocks.size] do
    let some block := source.blocks[sourceBlock]? | return false
    if sourceRow < block.length then break
    sourceRow := sourceRow - block.length
    sourceBlock := sourceBlock + 1
  let mut sliceBlock := 0
  let mut sliceRow := 0
  for _ in [:length] do
    let some original := source.blocks[sourceBlock]? | return false
    let some selected := sliced.blocks[sliceBlock]? | return false
    let some expected := original.get? sourceRow | return false
    unless selected.get? sliceRow == some expected do return false
    sourceRow := sourceRow + 1
    if sourceRow == original.length then
      sourceRow := 0
      sourceBlock := sourceBlock + 1
    sliceRow := sliceRow + 1
    if sliceRow == selected.length then
      sliceRow := 0
      sliceBlock := sliceBlock + 1
  return sliceBlock == sliced.blocks.size && sliceRow == 0

/-- Lossless region importing with a streaming comparison against the actual
    parsed columns. The old importer and its checked data remain unchanged. -/
elab "import_setup_slice " name:ident " from " path:str " native_table_id " id:num : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let columns ← artifact.columns.mapM fun column => do
    let sliced := sliceColumn column region.offset region.length
    match sliced.validate region.length babyBearModulus with
    | .error error => throwError "setup region slice failed: {error}"
    | .ok () => pure ()
    unless matchesSource column sliced region.offset region.length do
      throwError "setup region slice changed a parsed value"
    columnSyntax sliced
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    Airbender.Setup.TableData.mk $(quote region.length) 0 #v[$[$columns],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let regionName := mkIdent (name.getId.appendAfter "Region")
  elabCommand (← `(def $regionName : Airbender.Setup.Region :=
    Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns)))

/-- Pilot representation for an eight-bit setup column: one 2048-bit natural
number per 256 native rows. The importer still validates the parsed region and
compares every selected value to the source column before emitting literals.
This is data import, not a proof that a table satisfies an expected formula. -/
elab "import_setup_packed_bytes " name:ident " from " path:str
    " native_table_id " id:num " physical_column " physical:num : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let some original := artifact.columns[physical.getNat]?
    | throwError "setup physical column is absent"
  let sliced := sliceColumn original region.offset region.length
  match sliced.validate region.length babyBearModulus with
  | .error error => throwError "setup region slice failed: {error}"
  | .ok () => pure ()
  unless matchesSource original sliced region.offset region.length do
    throwError "setup region slice changed a parsed value"
  unless region.length % 256 == 0 do
    throwError "packed-byte region length must be a multiple of 256"
  let mut bytes := #[]
  for block in sliced.blocks do
    for index in [:block.length] do
      let some value := block.get? index
        | throwError "packed-byte source contains an absent value"
      unless value < 256 do
        throwError "packed-byte source value exceeds 255"
      bytes := bytes.push value
  unless bytes.size == region.length do
    throwError "packed-byte source length differs from region"
  let mut packed := #[]
  for row in [:region.length / 256] do
    let mut value := 0
    let mut place := 1
    for column in [:256] do
      value := value + bytes[row * 256 + column]! * place
      place := place * 256
    packed := packed.push value
  let literal ← arraySyntax (packed.map quote)
  elabCommand (← `(def $name : Array Nat := $literal))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))

/-- One shared copy of the exact artifact bytes for column-level imports. -/
elab "import_setup_source " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  match parse source with
  | .error error => throwError "setup import failed: {error}"
  | .ok _ => pure ()
  elabCommand (← `(def $name : String := $(quote source)))

/-- Import one physical column from a native region. Sharing the source string
    and compiling columns separately keeps large materialized tables bounded. -/
elab "import_setup_column " name:ident " from " path:str
    " native_table_id " id:num " physical_column " physical:num
    " source_bytes " shared:ident : command => do
  let source ← IO.FS.readFile path.getString
  let sourceName ← resolveGlobalConstNoOverload shared
  let sourceInfo ← getConstInfoDefn sourceName
  let .lit (.strVal sharedBytes) := sourceInfo.value
    | throwError "shared setup source must be an imported literal string"
  unless sourceInfo.type.isConstOf ``String && sharedBytes == source do
    throwError "shared setup source bytes differ from the artifact"
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let some original := artifact.columns[physical.getNat]?
    | throwError "setup physical column is absent"
  let sliced := sliceColumn original region.offset region.length
  match sliced.validate region.length babyBearModulus with
  | .error error => throwError "setup region slice failed: {error}"
  | .ok () => pure ()
  unless matchesSource original sliced region.offset region.length do
    throwError "setup region slice changed a parsed value"
  let column ← columnSyntax sliced
  elabCommand (← `(def $name : Airbender.Setup.Column := $column))
  let bytesName := mkIdent (name.getId.appendAfter "SourceBytes")
  let sourceIdent := mkIdent sourceName
  elabCommand (← `(def $bytesName : String := $sourceIdent))
  let regionName := mkIdent (name.getId.appendAfter "Region")
  elabCommand (← `(def $regionName : Airbender.Setup.Region :=
    Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns)))
  let columnName := mkIdent (name.getId.appendAfter "PhysicalColumn")
  elabCommand (← `(def $columnName : Nat := $(quote physical.getNat)))

end Airbender.Setup.Slices
