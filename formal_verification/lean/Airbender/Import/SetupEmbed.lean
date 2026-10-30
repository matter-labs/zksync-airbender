import Airbender.Import.Setup
import Airbender.Import.Coefficients
import Clean.Circuit.Operations
import Mathlib.Algebra.Field.ZMod

namespace Airbender.Setup
open Lean Elab Command

/-- Same signed lift as circuit coefficients, applied to already canonical
    setup data. In BabyBear this denotes exactly the exported field value. -/
def signedValue (value : Nat) : Int :=
  if value ≤ babyBearModulus / 2 then value else (value : Int) - babyBearModulus

theorem signedValue_cast (value : Nat) :
    (signedValue value : ZMod babyBearModulus) = (value : ZMod babyBearModulus) := by
  unfold signedValue
  split
  · rfl
  · simp

/-- Literal columns emitted from a checked setup JSON document. -/
structure TableData (width : Nat) where
  length : Nat
  offset : Nat
  columns : Vector Column width
  deriving Repr

def TableData.row (data : TableData width) (index : Fin data.length) : Vector Int width :=
  data.columns.map fun column => signedValue ((column.get? (data.offset + index.val)).getD 0)

def TableData.table {p : Nat} [Fact p.Prime] (name : String) (data : TableData width) :
    Table (ZMod p) (fields width) := .fromStatic {
  name := name
  length := data.length
  row index := (data.row index).map (fun (value : Int) => (value : ZMod p))
  index _ := 0
  Spec entry := ∃ index : Fin data.length,
    entry = (data.row index).map (fun (value : Int) => (value : ZMod p))
  contains_iff _ := Iff.rfl
}

def TableData.scalarTable {p : Nat} [Fact p.Prime] (name : String) (data : TableData 1) :
    Table (ZMod p) field := .fromStatic {
  name := name
  length := data.length
  row index := ((data.row index)[0] : ZMod p)
  index value := value.val
  Spec entry := ∃ index : Fin data.length, entry = ((data.row index)[0] : ZMod p)
  contains_iff _ := Iff.rfl
}

structure Imported (width : Nat) where
  data : TableData width
  range16 : TableData 1
  timestampRange : TableData 1
  regions : Array Region
  program : Option Program
  deriving Repr

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

private def programSyntax (program : Option Program) : CommandElabM (TSyntax `term) := do
  match program with
  | none => `(none)
  | some program =>
    let image ← columnSyntax program.image
    let text ← columnSyntax program.text
    `(some (Airbender.Setup.Program.mk $(quote program.image_words) $image $(quote program.text_words) $text))

/-- Import actual materialized rows, the program inputs and native table regions.
    File reading, parsing and emission have the same fidelity boundary as
    `import_clean`; arithmetic properties of the emitted data need Lean proofs. -/
elab "import_setup " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "setup import failed: {error}"
  let columns ← artifact.columns.mapM columnSyntax
  let range16 ← columnSyntax artifact.range16
  let timestamp ← columnSyntax artifact.timestamp_range
  let regions ← artifact.tables.mapM fun region =>
    `(Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length) $(quote region.width) $(quote region.key_columns))
  let program ← programSyntax artifact.program
  elabCommand (← `(def $name : Airbender.Setup.Imported $(quote artifact.columns.size) :=
    Airbender.Setup.Imported.mk
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$[$columns],*])
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$range16])
      (Airbender.Setup.TableData.mk $(quote artifact.trace_len) 0 #v[$timestamp])
      #[$[$regions],*] $program))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let circuitName := mkIdent (name.getId.appendAfter "CircuitSource")
  let json ← match Json.parse source with
    | .ok json => pure json
    | .error error => throwError "setup import failed: {error}"
  let circuit ← match json.getObjVal? "circuit" with
    | .ok circuit => pure circuit.compress
    | .error error => throwError "setup import failed: {error}"
  elabCommand (← `(def $circuitName : String := $(quote circuit)))

private def readArtifact (path : String) : CommandElabM (Artifact × String) := do
  let source ← IO.FS.readFile path
  match parse source with
  | .ok artifact => pure (artifact, source)
  | .error error => throwError "setup import failed: {error}"

private def emitData (name : TSyntax `ident) (length offset : Nat)
    (columns : Array Column) (source : String) : CommandElabM Unit := do
  let columns ← columns.mapM columnSyntax
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    Airbender.Setup.TableData.mk $(quote length) $(quote offset) #v[$[$columns],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))

/-- Restrict encoded data, retaining full blocks and slicing boundary blocks.
    This is independent of table contents; imports check every selected value. -/
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

private def expandedValues (column : Column) : Array (Option Nat) :=
  column.blocks.flatMap fun block =>
    (Array.range block.length).map block.get?

/-- A compact view of one native region, including every physical padding/tag
    column. Preserve its native position separately and check every re-encoded
    value against the parsed complete setup before emitting any data. -/
elab "import_setup_region " name:ident " from " path:str " native_table_id " id:num : command => do
  let (artifact, source) ← readArtifact path.getString
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let columns ← artifact.columns.mapM fun column => do
    let sliced := sliceColumn column region.offset region.length
    match sliced.validate region.length babyBearModulus with
    | .error error => throwError "setup region slice failed: {error}"
    | .ok () => pure ()
    unless expandedValues sliced ==
        (expandedValues column).extract region.offset (region.offset + region.length) do
      throwError "setup region slice changed a parsed value"
    pure sliced
  emitData name region.length 0 columns source
  let regionName := mkIdent (name.getId.appendAfter "Region")
  elabCommand (← `(def $regionName : Airbender.Setup.Region :=
    Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns)))

/-- Select one exported virtual range column, preserving its full padding. -/
elab "import_setup_range " name:ident " from " path:str " virtual_range_bits " bits:num : command => do
  let (artifact, source) ← readArtifact path.getString
  let column ← match bits.getNat with
    | 16 => pure artifact.range16
    | 19 => pure artifact.timestamp_range
    | _ => throwError "setup artifact exports only the native 16-/19-bit virtual ranges"
  emitData name artifact.trace_len 0 #[column] source

/-- Import the native generic-table extent using exported region metadata.
    Physical commitment padding is retained by `import_setup`; this view selects
    exactly the real rows of the tagged generic table. -/
elab "import_setup_generic " name:ident " from " path:str : command => do
  let (artifact, source) ← readArtifact path.getString
  let length := artifact.tables.foldl (fun extent region =>
    max extent (region.offset + region.length)) 0
  unless length > 0 do throwError "setup has no generic table regions"
  emitData name length 0 artifact.columns source
  let regions ← artifact.tables.mapM fun region =>
    `(Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length) $(quote region.width) $(quote region.key_columns))
  let regionsName := mkIdent (name.getId.appendAfter "Regions")
  elabCommand (← `(def $regionsName : Array Airbender.Setup.Region := #[$[$regions],*]))


/-- Select a real table region and columns using the exported native ID/offset.
    Column selection is checked against the unpadded native table width. -/
elab "import_setup_table " name:ident " from " path:str " native_table_id " id:num
    " select_native_columns " "[" indices:num,* "]" : command => do
  let (artifact, source) ← readArtifact path.getString
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup table ID {id.getNat} is absent"
  let columns ← indices.getElems.mapM fun index => do
    unless index.getNat < region.width do throwError "column is outside native table width"
    let some column := artifact.columns[index.getNat]? | throwError "setup column is absent"
    pure column
  unless !columns.isEmpty do throwError "table import requires at least one column"
  emitData name region.length region.offset columns source

private def compactColumnPrefix (column : Column) (length : Nat) : Column := Id.run do
  if length < 1048576 || column.blocks.size ≤ 1024 then return column
  let mut prefixBlocks : Array Block := #[]
  let mut rest : Array Block := #[]
  let mut position := 0
  for block in column.blocks do
    if position < length then
      if length < position + block.length then return column
      prefixBlocks := prefixBlocks.push block
    else rest := rest.push block
    position := position + block.length
  let values := prefixBlocks.flatMap fun block =>
    (Array.range block.length).map fun index => (block.get? index).getD 0
  if values.size != length then return column
  for period in #[16, 256, 4096, 65536] do
    if period < length && length % period == 0 then
      let pattern := values.extract 0 period
      let replacement := Block.periodic (length / period) 0 pattern
      if (values.mapIdx fun index value => replacement.get? index == some value).all id then
        return ⟨#[replacement] ++ rest⟩
  return column

private def splitColumnAt (column : Column) (offset : Nat) : Option (Column × Column) := Id.run do
  let mut before : Array Block := #[]
  let mut after : Array Block := #[]
  let mut position := 0
  for block in column.blocks do
    if position + block.length ≤ offset then
      before := before.push block
    else after := after.push block
    position := position + block.length
  if position < offset then return none
  return some (⟨before⟩, ⟨after⟩)

structure SizedBlock (size : Nat) where
  block : Block
  length_eq : block.length = size

def SizedBlock.affine (size first : Nat) (step : Int) : SizedBlock size :=
  ⟨.affine size first step, rfl⟩

def SizedBlock.dense {size : Nat} (values : Vector Nat size) : SizedBlock size :=
  ⟨.dense values.toArray, values.size_toArray⟩

def SizedBlock.periodic {size : Nat} (repetitions : Nat) (stride : Int) (values : Vector Nat size) :
    SizedBlock (repetitions * size) :=
  ⟨.periodic repetitions stride values.toArray, by
    change repetitions * values.toArray.size = repetitions * size
    rw [values.size_toArray]⟩

@[simp] theorem SizedBlock.block_length {size : Nat} (value : SizedBlock size) :
    value.block.length = size := value.length_eq

private def sharedBlockSyntax (block : Block) : CommandElabM (TSyntax `term) := do
  let valuesSyntax (values : Array Nat) : CommandElabM (TSyntax `term) := do
    if let some first := values[0]? then
      let run := (values.toList.takeWhile (· == first)).length
      if 1 < run && run < values.size && values.size % run == 0 then
        let compact := (Array.range (values.size / run)).map fun index =>
          (values[index * run]?).getD 0
        if (values.mapIdx fun index value => value == (compact[index / run]?).getD 0).all id then
          let literal ← arraySyntax (compact.map quote)
          return ← `(Vector.ofFn (fun index : Fin $(quote values.size) =>
            ($literal[index.val / $(quote run)]?).getD 0))
    let literal ← arraySyntax (values.map quote)
    `((⟨$literal, by simp⟩ : Vector Nat $(quote values.size)))
  match block with
  | .affine size first step =>
    let step ← if step ≥ 0 then `(Int.ofNat $(quote step.toNat))
      else `(Int.negSucc $(quote (-step - 1).toNat))
    `(Airbender.Setup.SizedBlock.affine $(quote size) $(quote first) $step)
  | .dense values =>
    let values ← valuesSyntax values
    `(Airbender.Setup.SizedBlock.dense $values)
  | .periodic repetitions stride values =>
    let stride ← if stride ≥ 0 then `(Int.ofNat $(quote stride.toNat))
      else `(Int.negSucc $(quote (-stride - 1).toNat))
    let values ← valuesSyntax values
    `(Airbender.Setup.SizedBlock.periodic $(quote repetitions) $stride $values)

/-- Import a complete generic table with separate column declarations.
The parsed values and source bytes match the ordinary generic import.
Separate declarations limit elaboration memory for tables with many blocks. -/
elab "import_setup_generic_columns " name:ident " from " path:str " native_table_id " id:num : command => do
  let (artifact, source) ← readArtifact path.getString
  let length := artifact.tables.foldl (fun extent region =>
    max extent (region.offset + region.length)) 0
  unless length > 0 do throwError "setup has no generic table regions"
  let some region := artifact.tables.find? (fun region => region.id == id.getNat)
    | throwError "setup split region is absent"
  let mut shared : Std.HashMap String (Block × TSyntax `term) := {}
  let mut columns : Array (TSyntax `term) := #[]
  let mut prefixes : Array (TSyntax `term) := #[]
  let mut suffixes : Array (TSyntax `term) := #[]
  let mut prefixLengths : Array (TSyntax `term) := #[]
  let mut controlOffsets : Array (TSyntax `term) := #[]
  let mut controlColumns : Array (TSyntax `term) := #[]
  let prefixLength := region.offset
  for (column, index) in artifact.columns.zipIdx do
    let column := compactColumnPrefix column prefixLength
    let some (before, after) := splitColumnAt column prefixLength
      | throwError "setup split region exceeds its parsed column"
    let actualLength := before.blocks.foldl (fun total block => total + block.length) 0
    prefixLengths := prefixLengths.push (quote actualLength)
    controlOffsets := controlOffsets.push (quote (prefixLength - actualLength))
    controlColumns := controlColumns.push (← columnSyntax (sliceColumn column region.offset region.length))
    let mut parts : Array (TSyntax `term) := #[]
    for (part, label) in #[(before, "Prefix"), (after, "Suffix")] do
      let mut blocks : Array (TSyntax `term) := #[]
      for block in part.blocks do
        let key := reprStr block
        let value ← if let some (original, value) := shared[key]? then do
          unless original = block do throwError "setup block sharing changed a parsed value"
          pure value
        else do
          let blockName := mkIdent (name.getId.appendAfter s!"Block{shared.size}")
          let literal ← sharedBlockSyntax block
          elabCommand (← `(def $blockName : Airbender.Setup.SizedBlock $(quote block.length) := $literal))
          let value ← `(($blockName).block)
          shared := shared.insert key (block, value)
          pure value
        blocks := blocks.push value
      let blockArray ← arraySyntax blocks
      let partName := mkIdent (name.getId.appendAfter s!"{label}{index}")
      elabCommand (← `(abbrev $partName : Airbender.Setup.Column := ⟨$blockArray⟩))
      parts := parts.push (← `(($partName : Airbender.Setup.Column)))
    let before := parts[0]!
    let after := parts[1]!
    prefixes := prefixes.push before
    suffixes := suffixes.push after
    let columnName := mkIdent (name.getId.appendAfter s!"Column{index}")
    elabCommand (← `(def $columnName : Airbender.Setup.Column := ⟨($before).blocks ++ ($after).blocks⟩))
    columns := columns.push (← `(($columnName : Airbender.Setup.Column)))
  let prefixesName := mkIdent (name.getId.appendAfter "Prefixes")
  let suffixesName := mkIdent (name.getId.appendAfter "Suffixes")
  let prefixLengthsName := mkIdent (name.getId.appendAfter "PrefixLengths")
  let controlOffsetsName := mkIdent (name.getId.appendAfter "ControlOffsets")
  elabCommand (← `(def $prefixesName : Vector Airbender.Setup.Column $(quote columns.size) := #v[$[$prefixes],*]))
  elabCommand (← `(def $suffixesName : Vector Airbender.Setup.Column $(quote columns.size) := #v[$[$suffixes],*]))
  elabCommand (← `(def $prefixLengthsName : Vector Nat $(quote columns.size) := #v[$[$prefixLengths],*]))
  elabCommand (← `(def $controlOffsetsName : Vector Nat $(quote columns.size) := #v[$[$controlOffsets],*]))
  let controlName := mkIdent (name.getId.appendAfter "Control")
  elabCommand (← `(def $controlName : Airbender.Setup.TableData $(quote columns.size) :=
    Airbender.Setup.TableData.mk $(quote region.length) 0 #v[$[$controlColumns],*]))
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    Airbender.Setup.TableData.mk $(quote length) 0 #v[$[$columns],*]))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
  let regions ← artifact.tables.mapM fun region =>
    `(Airbender.Setup.Region.mk $(quote region.id) $(quote region.offset) $(quote region.length)
      $(quote region.width) $(quote region.key_columns))
  let regionsName := mkIdent (name.getId.appendAfter "Regions")
  elabCommand (← `(def $regionsName : Array Airbender.Setup.Region := #[$[$regions],*]))

end Airbender.Setup
