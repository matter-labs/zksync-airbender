import Airbender.Import.SetupRegionEmbed

namespace Airbender.Setup.DecoderData
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


/-- Compare the exported block streams. Equal affine starts and strides cover
    every row of their overlap; all remaining values are compared individually.
    The parser validates every source block and emitSlice validates the slice.
    This changes no emitted data and introduces no table-generation rule. -/
private def matchesSource (source sliced : Column) (offset length : Nat) : Bool := Id.run do
  let mut sourceBlock := 0
  let mut sourceRow := offset
  for _ in [:source.blocks.size] do
    let some block := source.blocks[sourceBlock]? | return false
    if sourceRow < block.length then break
    sourceRow := sourceRow - block.length
    sourceBlock := sourceBlock + 1
  let mut sliceBlock := 0
  let mut sliceRow := 0
  let mut processed := 0
  for _ in [:source.blocks.size + sliced.blocks.size + 1] do
    if processed == length then
      return sliceBlock == sliced.blocks.size && sliceRow == 0
    let some original := source.blocks[sourceBlock]? | return false
    let some selected := sliced.blocks[sliceBlock]? | return false
    let count := min (length - processed)
      (min (original.length - sourceRow) (selected.length - sliceRow))
    if count == 0 then return false
    let sameAffine := match original, selected with
      | .affine _ first step, .affine _ other otherStep =>
          step == otherStep && (first : Int) + step * sourceRow ==
            (other : Int) + otherStep * sliceRow
      | _, _ => false
    unless sameAffine do
      for row in [:count] do
        let some value := original.get? (sourceRow + row) | return false
        unless selected.get? (sliceRow + row) == some value do return false
    processed := processed + count
    sourceRow := sourceRow + count
    sliceRow := sliceRow + count
    if sourceRow == original.length then
      sourceRow := 0
      sourceBlock := sourceBlock + 1
    if sliceRow == selected.length then
      sliceRow := 0
      sliceBlock := sliceBlock + 1
  return false

#guard matchesSource ⟨#[.affine 100 0 1]⟩ ⟨#[.affine 20 30 1]⟩ 30 20
#guard !matchesSource ⟨#[.affine 100 0 1]⟩ ⟨#[.affine 20 31 1]⟩ 30 20
#guard !matchesSource ⟨#[.affine 100 0 1]⟩ ⟨#[.affine 20 30 2]⟩ 30 20
#guard matchesSource ⟨#[.dense #[1, 2], .affine 100 3 0]⟩
  ⟨#[.dense #[2], .affine 20 3 0]⟩ 1 21

private def emitSlice (name : TSyntax `ident) (artifact : Artifact)
    (start length : Nat) : CommandElabM Unit := do
  let columns ← artifact.columns.mapM fun column => do
    let sliced := sliceColumn column start length
    match sliced.validate length babyBearModulus with
    | .error error => throwError "decoder setup slice failed: {error}"
    | .ok () => pure ()
    unless matchesSource column sliced start length do
      throwError "decoder setup slice changed a parsed value"
    columnSyntax sliced
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    Airbender.Setup.TableData.mk $(quote length) 0 #v[$[$columns],*]))

/-- Real decoder rows and the complete committed tail, from actual setup metadata. -/
elab "import_setup_decoder " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  unless artifact.circuit.has_decoder_lookup do
    throwError "setup artifact has no decoder table"
  let some program := artifact.program
    | throwError "decoder setup has no selected program payload"
  let start := artifact.circuit.offset_for_decoder_table
  let finish := artifact.circuit.total_tables_size
  let count := finish - start
  unless count == program.text_words do
    throwError "decoder real-row extent differs from selected text geometry"
  let mask := artifact.circuit.decode_table_columns_mask
  let tagged := artifact.circuit.tables_ids_in_generic_lookups
  unless mask.size == 9 &&
      (mask.filter id).size + (if tagged then 1 else 0) == artifact.columns.size do
    throwError "decoder physical columns differ from the exported mask"
  let prefixName := mkIdent (name.getId.appendAfter "PrefixTags")
  let leading ← if tagged then do
      let some tagColumn := artifact.columns[artifact.columns.size - 1]?
        | throwError "tagged decoder setup has no discriminator column"
      let leading := sliceColumn tagColumn 0 start
      match leading.validate start babyBearModulus with
      | .error error => throwError "decoder leading import failed: {error}"
      | .ok () => pure ()
      unless matchesSource tagColumn leading 0 start do
        throwError "decoder leading import changed a parsed discriminator"
      columnSyntax leading
    else do
      unless start == 0 do
        throwError "untagged decoder setup has an unsupported fixed-table leading"
      `(({blocks := #[]} : Airbender.Setup.Column))
  elabCommand (← `(def $prefixName : Airbender.Setup.Column := $leading))
  emitSlice name artifact start count
  let paddingName := mkIdent (name.getId.appendAfter "Padding")
  emitSlice paddingName artifact finish (artifact.trace_len - finish)
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let offsetName := mkIdent (name.getId.appendAfter "Offset")
  elabCommand (← `(def $offsetName : Nat := $(quote start)))
  let endName := mkIdent (name.getId.appendAfter "RealEnd")
  elabCommand (← `(def $endName : Nat := $(quote finish)))
  let traceName := mkIdent (name.getId.appendAfter "TraceLength")
  elabCommand (← `(def $traceName : Nat := $(quote artifact.trace_len)))
  let maskName := mkIdent (name.getId.appendAfter "ColumnsMask")
  let mask ← mask.mapM fun flag => if flag then `(true) else `(false)
  elabCommand (← `(def $maskName : Array Bool := #[$[$mask],*]))
  let taggedName := mkIdent (name.getId.appendAfter "Tagged")
  let tagged ← if tagged then `(true) else `(false)
  elabCommand (← `(def $taggedName : Bool := $tagged))

end Airbender.Setup.DecoderData
