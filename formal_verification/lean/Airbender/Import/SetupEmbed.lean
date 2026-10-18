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

end Airbender.Setup
