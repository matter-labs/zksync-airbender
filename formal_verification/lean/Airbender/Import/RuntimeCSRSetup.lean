import Airbender.Import.SetupEmbed

namespace Airbender.Setup.RuntimeCSR
open Lean Elab Command

structure Artifact where
  version : Nat
  field_modulus : Nat
  profile : String
  delegation_csrs : Array Nat
  allow_non_determinism : Bool
  generic_rows : Nat
  tables : Array Region
  deriving Repr, FromJson

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing runtime CSR JSON fields"

/-- Exact selected runtime configuration and geometry. Stored values are only
    checked for canonical literal encoding here; semantics are kernel obligations. -/
def Artifact.validate (artifact : Artifact) : Except String Unit := do
  unless artifact.version == 1 && artifact.field_modulus == mersenne31Modulus &&
      artifact.profile == "reduced_machine_csr_properties" do throw "unsupported runtime CSR profile"
  unless artifact.delegation_csrs == #[1984,1991] && artifact.allow_non_determinism do
    throw "unsupported runtime CSR public configuration"
  unless artifact.generic_rows == 4096 && artifact.tables.size == 1 do throw "unsupported runtime CSR extent"
  let some region := artifact.tables[0]? | throw "missing runtime CSR region"
  unless region.id == 25 && region.offset == 1507585 && region.data.length == 4096 &&
      region.data.columns.size == 4 do throw "unsupported runtime CSR geometry"
  for column in region.data.columns do column.validate 4096 mersenne31Modulus

def parse (source : String) : Except String Artifact := do
  let json ← Json.parse source
  exactKeys json #["version","field_modulus","profile","delegation_csrs","allow_non_determinism","generic_rows","tables"]
  for region in (← (← json.getObjVal? "tables").getArr?) do
    exactKeys region #["id","offset","data"]
    let data ← region.getObjVal? "data"
    exactKeys data #["length","columns"]
    for column in (← (← data.getObjVal? "columns").getArr?) do exactKeys column #["blocks"]
  let artifact : Artifact ← fromJson? json
  artifact.validate
  return artifact

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


/-- Emit the same-read validated literal bytes and explicit public configuration.
    No field value is inferred from a CSR recipe or the profile name. -/
elab "import_native_runtime_csr " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let artifact ← match parse source with
    | .ok artifact => pure artifact
    | .error error => throwError "runtime CSR import failed: {error}"
  let some region := artifact.tables[0]? | throwError "missing runtime CSR region"
  emitData name region.data region.offset
  let csrsName := mkIdent (name.getId.appendAfter "DelegationCSRs")
  elabCommand (← `(def $csrsName : Array Nat := $(quote artifact.delegation_csrs)))
  let nonDetName := mkIdent (name.getId.appendAfter "AllowNonDeterminism")
  elabCommand (← `(def $nonDetName : Bool := $(quote artifact.allow_non_determinism)))
  let sourceName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $sourceName : String := $(quote source)))
end Airbender.Setup.RuntimeCSR
