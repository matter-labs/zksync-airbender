import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Blake2Fixed
open Lean Elab Command

structure Artifact where
  version : Nat
  field_modulus : Nat
  profile : String
  generic_rows : Nat
  tables : Array Region
  deriving Repr, FromJson

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing native worker fixed fields"

def Artifact.validate (a : Artifact) : Except String Unit := do
  unless a.version == 1 && a.field_modulus == mersenne31Modulus &&
      a.profile == "blake2_extended_control_fixed" && a.generic_rows == 344384 && a.tables.size == 5 do
    throw "unsupported Blake2 fixed profile/extent"
  for (region,(id,offset,length)) in a.tables.zip #[(4,0,65536),(26,65536,64),(27,65600,256),(28,65856,16384),(29,82240,262144)] do
    unless region.id == id && region.offset == offset && region.data.length == length && region.data.columns.size == 4 do
      throw "unsupported Blake2 fixed geometry"
    for column in region.data.columns do column.validate length mersenne31Modulus

def parse (source : String) : Except String Artifact := do
  let json ← Json.parse source
  exactKeys json #["version","field_modulus","profile","generic_rows","tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id","offset","data"]
    let data ← region.getObjVal? "data"
    exactKeys data #["length","columns"]
    for column in (← (← data.getObjVal? "columns").getArr?) do exactKeys column #["blocks"]
  let a : Artifact ← fromJson? json
  a.validate
  return a

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

private def emitChunkedData (name : TSyntax `ident) (matrix : Matrix) (offset : Nat) :
    CommandElabM Unit := do
  let mut columns : Array (TSyntax `term) := #[]
  for (column,lane) in matrix.columns.zipIdx do
    let mut blocks : Array (TSyntax `term) := #[]
    for (stored,index) in column.blocks.zipIdx do
      let target := mkIdent (name.getId.appendAfter ("Column" ++ toString lane ++ "Block" ++ toString index))
      let block ← blockSyntax stored
      elabCommand (← `(def $target : Airbender.Setup.Block := $block))
      blocks := blocks.push (← `($target))
    let encoded ← arraySyntax blocks
    let target := mkIdent (name.getId.appendAfter ("Column" ++ toString lane))
    elabCommand (← `(def $target : Airbender.Setup.Column := ⟨$encoded⟩))
    columns := columns.push (← `($target))
  elabCommand (← `(def $name : Airbender.Setup.TableData $(quote columns.size) :=
    ⟨$(quote matrix.length), $(quote offset), #v[$[$columns],*]⟩))

/-- Quote every actual native literal region and the same-read complete source.
    Output semantics and all-row tag/domain properties are kernel obligations. -/
elab "import_native_blake2_fixed " name:ident " from " path:str " native_region " selected:num : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with | .ok a => pure a | .error e => throwError "native Blake2 fixed import failed: {e}"
  let some region := artifact.tables.find? (fun region => region.id == selected.getNat) | throwError "unknown native worker region"
  emitChunkedData (mkIdent (name.getId.appendAfter ("T" ++ toString region.id))) region.data region.offset
  let sourceName := mkIdent (name.getId.appendAfter ("T" ++ toString region.id ++ "SourceBytes"))
  elabCommand (← `(def $sourceName : String := $(quote source)))

end Airbender.Setup.Blake2Fixed
