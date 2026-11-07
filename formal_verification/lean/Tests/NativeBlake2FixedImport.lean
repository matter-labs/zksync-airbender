import Airbender.Review.Circuits.Blake2Worker.Tables

open Airbender Airbender.Setup Airbender.Setup.Blake2Fixed Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

private def changed (json : Json) (key : String) (value : Json) : IO Unit := do
  let altered ← IO.ofExcept (replaceField json key value)
  check (rejected (Airbender.Setup.Blake2Fixed.parse altered.compress)) s!"worker fixed rejects {key}"

private def changedRegion (json : Json) (key : String) (value : Json) : IO Unit := do
  let tables ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "tables")).getArr?)
  let some table := tables[0]? | throw (IO.userError "missing worker region")
  let altered ← IO.ofExcept (replaceField table key value)
  changed json "tables" (toJson (tables.set! 0 altered))

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/setup/blake2-fixed-native.json"
    check (source == Airbender.Blake2Worker.Fixed.dataT4SourceBytes &&
      source == Airbender.Blake2Worker.Fixed.dataT26SourceBytes &&
      source == Airbender.Blake2Worker.Fixed.dataT27SourceBytes &&
      source == Airbender.Blake2Worker.Fixed.dataT28SourceBytes &&
      source == Airbender.Blake2Worker.Fixed.dataT29SourceBytes) "five worker regions retain same-read complete bytes"
    let a ← IO.ofExcept (Airbender.Setup.Blake2Fixed.parse source)
    check (a.generic_rows == 344384 && a.tables.size == 5) "complete native worker pool extent"
    let json ← IO.ofExcept (Json.parse source)
    changed json "version" (toJson (2 : Nat))
    changed json "field_modulus" (toJson (2147483648 : Nat))
    changed json "profile" (toJson "reduced_machine_fixed")
    changed json "generic_rows" (toJson (344383 : Nat))
    changed json "tables" (toJson (#[] : Array Json))
    changed json "extra" Json.null
    changedRegion json "id" (toJson (0 : Nat))
    changedRegion json "offset" (toJson (1 : Nat))
    changedRegion json "extra" Json.null
    let some region := a.tables[0]? | throw (IO.userError "missing worker byte region")
    let changedFirst (matrix : Matrix) : Airbender.Setup.Blake2Fixed.Artifact :=
      {a with tables := a.tables.set! 0 {region with data := matrix}}
    check (rejected ((changedFirst {region.data with length := 65535}).validate)) "reject worker matrix length"
    check (rejected ((changedFirst {region.data with columns := region.data.columns.extract 0 3}).validate)) "reject missing worker lane"
    let empty : Column := ⟨#[]⟩
    check (rejected ((changedFirst {region.data with columns := #[empty,empty,empty,empty]}).validate)) "reject missing worker literals"
    let oversized : Column := ⟨#[.affine 65536 2147483647 0]⟩
    check (rejected ((changedFirst {region.data with columns := #[oversized,oversized,oversized,oversized]}).validate)) "reject noncanonical worker table fields"
    let negative : Column := ⟨#[.affine 65536 0 (-1)]⟩
    check (rejected ((changedFirst {region.data with columns := #[negative,negative,negative,negative]}).validate)) "reject negative worker literals"
    let zeroBlock : Column := ⟨#[.affine 0 0 0]⟩
    check (rejected ((changedFirst {region.data with columns := #[zeroBlock,zeroBlock,zeroBlock,zeroBlock]}).validate)) "reject empty worker blocks"
    let zeros : Column := ⟨#[.affine 65536 0 0]⟩
    check (!(rejected ((changedFirst {region.data with columns := #[zeros,zeros,zeros,zeros]}).validate))) "literal intake does not certify worker row semantics"
    check (rejected ({a with tables := a.tables.reverse}.validate)) "reject reordered worker regions"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
