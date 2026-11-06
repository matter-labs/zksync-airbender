import Airbender.Review.Circuits.ReducedMachine.Theorems
import Airbender.Review.Circuits.ReducedMachine.Artifact

open Airbender Airbender.Setup Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)
private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false
private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/reduced-native-layout.json"
    check (source == ReducedMachine.Native.importedConstraintsSourceBytes) "regenerated native complete source bytes"
    let c ← IO.ofExcept (parseCircuit source)
    check (c.degree_2_constraints.size == 112 && c.degree_1_constraints.size == 5 &&
      c.variable_mapping.entries.size == 142 && c.witness_layout.total_width == 107)
      "all regenerated native equations and variables"
    let setup ← IO.ofExcept c.setupColumns
    check (setup.genericRows == 5771521 && setup.traceLength == 8388608 && setup.width == 16)
      "regenerated native setup geometry includes truncation"
    check (c.table_offsets[47]? == some 5705985 && c.table_offsets[48]? == some 5771521)
      "actual native truncation start and final extent"
    check ((← IO.ofExcept c.requestColumns) == some ⟨92,94,some 93,3⟩)
      "regenerated request coordinates are not historical coordinates"
    let arguments ← IO.ofExcept c.reducedArgumentColumns
    check (arguments.initialAddress == #v[126,127] && arguments.terminalValue == #v[128,129] &&
      arguments.terminalTime == #v[130,131] && arguments.addressAux == #v[122,123] &&
      arguments.addressBorrows == #v[124,125]) "regenerated native initialization coordinates"
    let historicalSource ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (historicalSource == ReducedMachine.importedConstraintsSourceBytes) "historical artifact preserved separately"
    let old ← IO.ofExcept (parseCircuit historicalSource)
    check (old.degree_2_constraints.size == 114 && old.total_tables_size == 5705985 &&
      old.variable_mapping.entries.size == 141) "historical and regenerated targets remain distinct"
    check (rejected ({c with total_tables_size := 5705985}.validate)) "reject crossed historical/native extent"
    check (rejected ({c with table_offsets := old.table_offsets}.validate)) "reject crossed historical/native offsets"
    check (rejected ({old with table_offsets := c.table_offsets}.validate)) "reject native offsets on historical target"
    check (rejected ({c with trace_len := 16777216}.validate)) "reject wrong native trace profile"
    let fixedSource ← IO.FS.readFile "artifacts/setup/reduced-fixed-native.json"
    check (fixedSource == ReducedMachine.NativeFixed.dataSourceBytes) "complete native fixed-pool source bytes"
    let fixed ← IO.ofExcept (ReducedFixed.parse fixedSource)
    check (fixed.generic_rows == c.total_tables_size && fixed.tables.size == 14)
      "complete actual native pool agrees with regenerated geometry"
    check (fixed.«public».image_words == 8 && fixed.«public».delegation_csrs == #[1988,1989] &&
      fixed.«public».allow_non_determinism) "actual public image and delegation configuration retained"
    check (rejected ({fixed with generic_rows := 5705985}.validate)) "reject historical pool extent"
    check (rejected ({fixed with tables := fixed.tables.extract 0 13}.validate)) "reject missing native truncation table"
    check (rejected ({fixed with «public» := {fixed.«public» with delegation_csrs := #[4096]}}.validate))
      "reject out-of-range public CSR"
    check (rejected ({fixed with «public» := {fixed.«public» with allow_non_determinism := false}}.validate))
      "reject nonnative nondeterminism setting"
    check (rejected ({fixed with «public» := {fixed.«public» with image_words := 1048577}}.validate))
      "reject oversized public ROM prefix"
    for (region,index) in fixed.tables.zipIdx do
      let altered := {region with offset := region.offset + 1}
      check (rejected ({fixed with tables := fixed.tables.set! index altered}.validate))
        s!"reject altered native region placement {region.id}"
    let some last := fixed.tables[13]? | throw (IO.userError "missing native truncation")
    check (rejected ({fixed with tables := fixed.tables.set! 13 {last with data :=
      {last.data with length := 65535}}}.validate)) "reject altered native truncation extent"
    check (rejected ({fixed with tables := fixed.tables.set! 13 {last with data :=
      {last.data with columns := last.data.columns.extract 0 3}}}.validate)) "reject missing native fixed lane"
    let invalidImage : Column := ⟨#[.affine 8 4294967296 0]⟩
    check (rejected ({fixed with «public» := {fixed.«public» with image := invalidImage}}.validate))
      "reject non-u32 public image word"
    let json ← IO.ofExcept (Json.parse fixedSource)
    let extra ← IO.ofExcept (replaceField json "extra" Json.null)
    check (rejected (ReducedFixed.parse extra.compress)) "reject extra full-pool root field"
    let inputs ← IO.ofExcept (json.getObjVal? "public")
    let inputs ← IO.ofExcept (replaceField inputs "extra" Json.null)
    let extra ← IO.ofExcept (replaceField json "public" inputs)
    check (rejected (ReducedFixed.parse extra.compress)) "reject extra public-input field"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
