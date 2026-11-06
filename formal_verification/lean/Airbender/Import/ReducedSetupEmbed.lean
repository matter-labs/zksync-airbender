import Airbender.Import.SetupEmbed
import Airbender.Import.ReducedSetup

namespace Airbender.Setup.Reduced
open Lean Elab Command

-- Literal emission helpers copied unchanged from Import/SetupEmbed.lean.
-- Keeping this importer separate avoids altering established family importers.
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

/-- Parse and quote the same source bytes, emitting only validated literal blocks. -/
elab "import_native_reduced_sign_high " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parseSignHigh source with
    | .ok artifact => pure artifact
    | .error error => throwError "native reduced sign/high-byte import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing native reduced sign/high-byte region"
  emitData name region.data region.offset
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))

end Airbender.Setup.Reduced
