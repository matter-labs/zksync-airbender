import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimeCSR

open Airbender Airbender.Setup Airbender.Setup.RuntimeCSR Lean
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
  check (rejected (Airbender.Setup.RuntimeCSR.parse altered.compress)) s!"runtime CSR rejects {key}"

private def changedRegion (json : Json) (key : String) (value : Json) : IO Unit := do
  let regions ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "tables")).getArr?)
  let some region := regions[0]? | throw (IO.userError "missing region")
  let altered ← IO.ofExcept (replaceField region key value)
  changed json "tables" (toJson #[altered])

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/setup/reduced-runtime-csr-native.json"
    check (source == ReducedMachine.NativeRuntimeCSR.dataSourceBytes) "runtime CSR complete source bytes"
    let artifact ← IO.ofExcept (Airbender.Setup.RuntimeCSR.parse source)
    check (artifact.generic_rows == 4096 && artifact.tables.size == 1 &&
      artifact.delegation_csrs == #[1984,1991] && artifact.allow_non_determinism) "runtime CSR native region extent"
    let json ← IO.ofExcept (Json.parse source)
    changed json "version" (toJson (2 : Nat))
    changed json "field_modulus" (toJson (2147483648 : Nat))
    changed json "profile" (toJson "shift_binop_scalar_regions")
    changed json "generic_rows" (toJson (65535 : Nat))
    changed json "tables" (toJson (#[] : Array Json))
    changed json "extra" Json.null
    changed json "delegation_csrs" (toJson (#[1988,1989] : Array Nat))
    changed json "allow_non_determinism" (toJson false)
    changedRegion json "id" (toJson (17 : Nat))
    changedRegion json "offset" (toJson (0 : Nat))
    changedRegion json "extra" Json.null
    let badMatrix := Json.mkObj [("length",toJson (65535 : Nat)),("columns",toJson (#[] : Array Json))]
    changedRegion json "data" badMatrix
    let some region := artifact.tables[0]? | throw (IO.userError "missing runtime CSR region")
    check (rejected (Artifact.validate {artifact with tables := #[{region with data :=
      {region.data with columns := region.data.columns.extract 0 3}}]})) "reject missing runtime CSR lane"
    let empty : Column := ⟨#[]⟩
    check (rejected (Artifact.validate {artifact with tables := #[{region with data :=
      {region.data with columns := #[empty,empty,empty,empty]}}]})) "reject missing runtime CSR rows"
    let noncanonical : Column := ⟨#[.affine 4096 2147483647 0]⟩
    check (rejected (Artifact.validate {artifact with tables := #[{region with data :=
      {region.data with columns := #[noncanonical,noncanonical,noncanonical,noncanonical]}}]}))
      "reject noncanonical runtime CSR residues"
    let negative : Column := ⟨#[.affine 4096 0 (-1)]⟩
    check (rejected (Artifact.validate {artifact with tables := #[{region with data :=
      {region.data with columns := #[negative,negative,negative,negative]}}]}))
      "reject negative runtime CSR block values"
    let zero : Column := ⟨#[.affine 4096 0 0]⟩
    check (!(rejected (Artifact.validate {artifact with tables := #[{region with data :=
      {region.data with columns := #[zero,zero,zero,zero]}}]})))
      "parsing literal rows does not assert their semantics"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
