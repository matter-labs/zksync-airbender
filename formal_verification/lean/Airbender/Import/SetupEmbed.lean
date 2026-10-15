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

/-- Compact literal data only after comparing every parsed element. These
    constructors do not select a table recipe or infer unexported values. -/
private def valuesSyntax (values : Array Nat) : CommandElabM (TSyntax `term) := do
  if let some first := values[0]? then
    if values.all (· == first) then
      return ← `(Array.replicate $(quote values.size) $(quote first))
    if (values.mapIdx fun i value => value == i).all id then
      return ← `(Array.range $(quote values.size))
    if (values.mapIdx fun i value => value == (first + i) % values.size).all id then
      return ← `(Array.ofFn (fun i : Fin $(quote values.size) =>
        ($(quote first) + i.val) % $(quote values.size)))
  let values := values.map quote
  `(#[$[$values],*])

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
  `(({blocks := #[$[$blocks],*]} : Airbender.Setup.Column))

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

end Airbender.Setup
