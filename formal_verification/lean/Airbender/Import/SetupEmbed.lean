import Airbender.Import.Setup
import Mathlib.Algebra.Field.ZMod

namespace Airbender.Setup
open Lean Elab Command

/-- Exported local rows. Native placement is metadata, not an index into these columns. -/
structure TableData (width : Nat) where
  length : Nat
  nativeOffset : Nat
  columns : Vector Column width
  deriving Repr

def TableData.rowNat (data : TableData width) (index : Fin data.length) : Vector Nat width :=
  data.columns.map fun column => (column.get? index.val).getD 0

def TableData.row {p : Nat} (data : TableData width) (index : Fin data.length) : Vector (ZMod p) width :=
  (data.rowNat index).map Nat.cast

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

private def emitData (name : TSyntax `ident) (matrix : Matrix) (offset : Nat) : CommandElabM Unit := do
  let columns ← matrix.columns.mapM columnSyntax
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    ⟨$(quote matrix.length), $(quote offset), #v[$[$columns],*]⟩))

/-- Emit literal native rows and public program inputs. Parsing/emission fidelity
    is separate from the kernel-checked statements about the emitted values. -/
elab "import_native_setup " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "native setup import failed: {error}"
  for (region, suffix) in artifact.tables.zip #["Zero", "Separator", "ROM"] do
    emitData (mkIdent (name.getId.appendAfter suffix)) region.data region.offset
  emitData (mkIdent (name.getId.appendAfter "Decoder")) artifact.decoder 0
  emitData (mkIdent (name.getId.appendAfter "Range16")) artifact.range16 0
  for (column, suffix) in #[(artifact.program.image, "Image"), (artifact.program.text, "Text")] do
    let column ← columnSyntax column
    let target := mkIdent (name.getId.appendAfter suffix)
    elabCommand (← `(def $target : Airbender.Setup.Column := $column))
  let textWords := mkIdent (name.getId.appendAfter "TextWords")
  elabCommand (← `(def $textWords : Nat := $(quote artifact.program.text_words)))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))

/-- Import both actual native scalar prefixes without selecting values by a
    recipe. Shared compiled layout guards establish scalar placement at 0/1. -/
elab "import_native_scalars " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseScalars source with
    | .ok artifact => pure artifact
    | .error error => throwError "native scalar import failed: {error}"
  emitData (mkIdent (name.getId.appendAfter "Range16")) artifact.range16 0
  emitData (mkIdent (name.getId.appendAfter "Timestamp19")) artifact.timestamp19 1

/-- Import a native arithmetic decoder and its public text as literal data.
    No decoder recipe or semantic equivalence is inserted by this command. -/
elab "import_native_decoder " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseDecoder source with
    | .ok artifact => pure artifact
    | .error error => throwError "native decoder import failed: {error}"
  emitData (mkIdent (name.getId.appendAfter "Decoder")) artifact.decoder 0
  let column ← columnSyntax artifact.text
  let target := mkIdent (name.getId.appendAfter "Text")
  elabCommand (← `(def $target : Airbender.Setup.Column := $column))
  let textWords := mkIdent (name.getId.appendAfter "TextWords")
  elabCommand (← `(def $textWords : Nat := $(quote artifact.text_words)))

/-- Import the separate native signed control decoder as literal public data.
    No decoder recipe or semantic equivalence is inserted by this command. -/
elab "import_native_control_decoder " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseControlDecoder source with
    | .ok artifact => pure artifact
    | .error error => throwError "native decoder import failed: {error}"
  emitData (mkIdent (name.getId.appendAfter "Decoder")) artifact.decoder 0
  let column ← columnSyntax artifact.text
  let target := mkIdent (name.getId.appendAfter "Text")
  elabCommand (← `(def $target : Airbender.Setup.Column := $column))
  let textWords := mkIdent (name.getId.appendAfter "TextWords")
  elabCommand (← `(def $textWords : Nat := $(quote artifact.text_words)))

/-- Literal native sentinel data only; its meaning is proved in the kernel. -/
elab "import_native_decoder_padding " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseDecoderPadding source with
    | .ok artifact => pure artifact
    | .error error => throwError "native decoder padding import failed: {error}"
  let values := artifact.row.map quote
  elabCommand (← `(def $name : Vector Nat 10 := #v[$[$values],*]))

/-- Import complete native tagged control rows as literal values only. -/
elab "import_native_control " name:ident " from " path:str : command => do
  let artifact ← match parseControl (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native control table import failed: {error}"
  for (region, suffix) in artifact.tables.zip #["Cleanup", "Conditional"] do
    emitData (mkIdent (name.getId.appendAfter suffix)) region.data region.offset

/-- Literal values from the native unsigned mul/div table driver, retaining ID 8. -/
elab "import_native_small_range " name:ident " from " path:str : command => do
  let artifact ← match parseSmallRange (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native byte-table import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native byte table"
  emitData name region.data region.offset

/-- Literal actual native shift/binop preprocessing with an empty CSR allow-list.
    This does not import dynamic lookup constraints or supply instruction semantics. -/
elab "import_native_shift_decoder " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseShiftDecoder source with
    | .ok artifact => pure artifact
    | .error error => throwError "native shift decoder import failed: {error}"
  emitData (mkIdent (name.getId.appendAfter "Decoder")) artifact.decoder 0
  let column ← columnSyntax artifact.text
  let textName := mkIdent (name.getId.appendAfter "Text")
  elabCommand (← `(def $textName : Airbender.Setup.Column := $column))
  let countName := mkIdent (name.getId.appendAfter "TextWords")
  elabCommand (← `(def $countName : Nat := $(quote artifact.text_words)))

/-- Literal actual native binary prefix, including the conditional zero row. -/
elab "import_native_binary " name:ident " from " path:str : command => do
  let artifact ← match parseBinary (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native binary prefix import failed: {error}"
  for (region,suffix) in artifact.tables.zip #["Zero","Xor","Or","And"] do
    emitData (mkIdent (name.getId.appendAfter suffix)) region.data region.offset

/-- Literal native truncation, sign-fill and zero-padded range rows. -/
elab "import_native_shift_scalars " name:ident " from " path:str : command => do
  let artifact ← match parseShiftScalars (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native shift scalar import failed: {error}"
  for (region,suffix) in artifact.tables.zip #["Truncate","SignFill","Range"] do
    emitData (mkIdent (name.getId.appendAfter suffix)) region.data region.offset

/-- Literal native low-input logical-right-shift rows only. -/
elab "import_native_srl_low " name:ident " from " path:str : command => do
  let artifact ← match parseSrlLow (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native SRL-low import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native SRL-low table"
  emitData name region.data region.offset

/-- Literal native high-input logical-left-shift rows only. -/
elab "import_native_sll_high " name:ident " from " path:str : command => do
  let artifact ← match parseSllHigh (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native SLL-high import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native SLL-high table"
  emitData name region.data region.offset

/-- Literal native low-input logical-left-shift rows only. -/
elab "import_native_sll_low " name:ident " from " path:str : command => do
  let artifact ← match parseSllLow (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native SLL-low import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native SLL-low table"
  emitData name region.data region.offset

/-- Literal native high-input logical-right-shift rows only. -/
elab "import_native_srl_high " name:ident " from " path:str : command => do
  let artifact ← match parseSrlHigh (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native SRL-high import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native SRL-high table"
  emitData name region.data region.offset


/-- Literal native CSR-properties rows only, without operation semantics. -/
elab "import_native_shift_csr_properties " name:ident " from " path:str : command => do
  let artifact ← match parseShiftCsrProperties (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native CSR-properties import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native CSR-properties table"
  emitData name region.data region.offset

/-- Literal native v2 subword offset/trap rows. No table recipe is synthesized. -/
elab "import_native_subword_offset " name:ident " from " path:str : command => do
  let artifact ← match parseSubwordOffset (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native subword offset import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native subword offset table"
  emitData name region.data region.offset

/-- Literal native v2 subword load-data rows. No table recipe is synthesized. -/
elab "import_native_subword_load " name:ident " from " path:str : command => do
  let artifact ← match parseSubwordLoad (← IO.FS.readFile path.getString) with
    | .ok artifact => pure artifact
    | .error error => throwError "native subword load import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native subword load table"
  -- Share actual literal blocks/columns so reducing one field never rebuilds
  -- the full matrix. Every value still comes from the validated native export.
  let mut columns : Array (TSyntax `term) := #[]
  for lane in [:region.data.columns.size] do
    let some column := region.data.columns[lane]? | throwError "missing native load column"
    let mut blocks : Array (TSyntax `term) := #[]
    for index in [:column.blocks.size] do
      let some block := column.blocks[index]? | throwError "missing native load block"
      let term ← if let .periodic count stride values := block then do
          let target := mkIdent (name.getId.appendAfter s!"Values{lane}_{index}")
          let literal ← valuesSyntax values
          elabCommand (← `(def $target : Array Nat := $literal))
          let stride ← if stride ≥ 0 then `(Int.ofNat $(quote stride.toNat))
            else `(Int.negSucc $(quote (-stride - 1).toNat))
          `(Airbender.Setup.Block.periodic $(quote count) $stride $target)
        else blockSyntax block
      let target := mkIdent (name.getId.appendAfter s!"Block{lane}_{index}")
      elabCommand (← `(def $target : Airbender.Setup.Block := $term))
      blocks := blocks.push (← `($target))
    let target := mkIdent (name.getId.appendAfter s!"Column{lane}")
    elabCommand (← `(def $target : Airbender.Setup.Column := ⟨#[$[$blocks],*]⟩))
    columns := columns.push (← `($target))
  elabCommand (← `(def $name : Airbender.Setup.TableData 4 :=
    ⟨$(quote region.data.length), $(quote region.offset), #v[$[$columns],*]⟩))

end Airbender.Setup
