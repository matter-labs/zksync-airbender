import Airbender.Import.SetupEmbed
import Airbender.Review.Circuits.Bigint.Tables.Setup
import Airbender.Review.Circuits.Blake2G.Tables.ControllerData
import Airbender.Review.Circuits.Keccak.Tables.ControllerData
import Airbender.Review.Circuits.Blake2G.Tables.XorData
import Airbender.Review.Circuits.Blake2Round.Tables.XorData

namespace Tests.SetupImport
open Airbender Lean

import_setup imported from "artifacts/setup/decoder-smoke.json"

theorem imported_shape : imported.data.length = 524288 ∧ imported.regions.size = 2 := by decide

theorem unsupported_decoder_sentinel :
    (imported.data.row ⟨8195, by decide⟩)[0] = -1 := by
  simp only [Setup.TableData.row, Vector.getElem_map]
  decide

theorem real_pc_zero :
    (imported.data.row ⟨8193, by decide⟩)[0] = 0 ∧
    (imported.data.row ⟨8193, by decide⟩)[8] = 46 := by
  simp only [Setup.TableData.row, Vector.getElem_map]
  decide

theorem range16_last : imported.range16.columns[0].get? 65535 = some 65535 := by decide

theorem range16_padding : imported.range16.columns[0].get? 65536 = some 0 := by decide

theorem timestamp_last :
    imported.timestampRange.columns[0].get? 524287 = some 524287 := by decide

theorem program_words :
    imported.program.bind (fun program => program.image.get? 0) = some 19 ∧
    imported.program.bind (fun program => program.text.get? 2) = some 111 := by decide

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def check (condition : Bool) (label : String) : IO Unit :=
  if condition then IO.println s!"PASS {label}"
  else throw (IO.userError s!"FAIL {label}")

private def values (column : Setup.Column) : Array (Option Nat) :=
  column.blocks.flatMap fun block => (Array.range block.length).map block.get?

private def checkXorRegions (label source : String) (artifact : Setup.Artifact)
    (data : Fin 5 → Setup.TableData width) (regions : Fin 5 → Setup.Region)
    (sources : Vector String 5) : IO Unit := do
  for k in List.finRange 5 do
    let imported := data k
    let region := regions k
    check (sources[k] == source && artifact.tables.contains region &&
      imported.length == region.length && imported.offset == 0 &&
      imported.columns.size == artifact.columns.size)
      s!"{label} XOR region {region.id}: exact source, metadata and physical geometry"
    check (imported.columns.toArray.zipIdx.all fun (column, index) =>
      some (values column) == artifact.columns[index]?.map (fun original =>
        (values original).extract region.offset (region.offset + region.length)))
      s!"{label} XOR region {region.id}: every key, output, padding and tag equals JSON"

def run : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/decoder-smoke.json"
  check (source == importedSourceBytes) "setup source bytes equal embedded artifact"
  let .ok artifact := Setup.parse source | throw (IO.userError "setup artifact failed import")
  check (artifact.columns == imported.data.columns.toArray)
    "every emitted setup value equals the parsed data"
  let bigintSource ← IO.FS.readFile "artifacts/setup/bigint.json"
  let .ok bigint := Setup.parse bigintSource
    | throw (IO.userError "bigint setup artifact failed import")
  check (bigintSource == Bigint.importedSetupSourceBytes &&
    bigint.columns == Bigint.importedSetup.columns.toArray)
    "every bigint constant/range/cyclic template equals the parsed data"
  let extent := bigint.tables.foldl (fun size region => max size (region.offset + region.length)) 0
  check (Bigint.importedSetup.length == extent && extent == 1390592 &&
    Bigint.importedSetup.offset == 0 && Bigint.importedSetup.columns.size == 3)
    "bigint consumers select the exact native generic-table extent"
  let controllerSource ← IO.FS.readFile "artifacts/setup/blake-g.json"
  let .ok controllerSetup := Setup.parse controllerSource
    | throw (IO.userError "BLAKE2 G setup artifact failed import")
  let some controllerRegion := controllerSetup.tables.find? (fun region => region.id == 28)
    | throw (IO.userError "BLAKE2 G controller region absent")
  check (controllerSource == Blake2G.controllerDataSourceBytes &&
    controllerRegion == Blake2G.controllerDataRegion &&
    Blake2G.controllerData.length == controllerRegion.length &&
    Blake2G.controllerData.offset == 0 &&
    Blake2G.controllerData.columns.size == controllerSetup.columns.size)
    "BLAKE2 G controller preserves source bytes and native region metadata"
  check ((Array.range controllerRegion.length).all fun row =>
    Blake2G.controllerData.columns.toArray.zipIdx.all fun (column, index) =>
      column.get? row ==
        controllerSetup.columns[index]?.bind (fun original =>
          original.get? (controllerRegion.offset + row)))
    "every BLAKE2 G controller key, output, padding and tag equals the parsed data"
  checkXorRegions "BLAKE2 G" controllerSource controllerSetup Blake2G.xorData Blake2G.xorRegion
    #v[Blake2G.xor8DataSourceBytes, Blake2G.xor3DataSourceBytes,
      Blake2G.xor4DataSourceBytes, Blake2G.xor7DataSourceBytes, Blake2G.xor9DataSourceBytes]
  let roundSource ← IO.FS.readFile "artifacts/setup/blake-round.json"
  let .ok roundSetup := Setup.parse roundSource
    | throw (IO.userError "extended BLAKE setup artifact failed import")
  checkXorRegions "extended BLAKE" roundSource roundSetup Blake2Round.xorData Blake2Round.xorRegion
    #v[Blake2Round.xor8DataSourceBytes, Blake2Round.xor3DataSourceBytes,
      Blake2Round.xor4DataSourceBytes, Blake2Round.xor7DataSourceBytes, Blake2Round.xor9DataSourceBytes]
  let keccakSource ← IO.FS.readFile "artifacts/setup/keccak.json"
  let .ok keccakSetup := Setup.parse keccakSource
    | throw (IO.userError "Keccak setup artifact failed import")
  let some keccakRegion := keccakSetup.tables.find? (fun region => region.id == 37)
    | throw (IO.userError "Keccak controller region absent")
  check (keccakSource == Keccak.controllerDataSourceBytes &&
    keccakRegion == Keccak.controllerDataRegion &&
    Keccak.controllerData.length == keccakRegion.length &&
    Keccak.controllerData.offset == 0 &&
    Keccak.controllerData.columns.size == keccakSetup.columns.size)
    "Keccak controller preserves source bytes and native region metadata"
  check ((Array.range keccakRegion.length).all fun row =>
    Keccak.controllerData.columns.toArray.zipIdx.all fun (column, index) =>
      column.get? row == keccakSetup.columns[index]?.bind (fun original =>
        original.get? (keccakRegion.offset + row)))
    "every Keccak controller key, output and tag equals the parsed data"
  check (artifact.trace_len == imported.data.length && artifact.columns.size == 9 &&
    artifact.tables.size == 2 && artifact.circuit.structured_statements.size == 30)
    "complete setup and its native circuit decoded together"
  check (rejected ({artifact with version := 2}.validate)) "unknown setup version rejected"
  check (rejected ({artifact with field_modulus := 17}.validate)) "foreign setup field rejected"
  check (rejected ({artifact with trace_len := 123}.validate)) "non-power-of-two setup rejected"
  check (rejected ({artifact with program := none}.validate)) "decoder setup without program inputs rejected"
  check (rejected ({artifact with columns := artifact.columns.pop}.validate))
    "missing setup column rejected"
  let bad : Setup.Column := ⟨#[.affine 524288 babyBearModulus 0]⟩
  check (rejected ({artifact with columns := artifact.columns.set! 0 bad}.validate))
    "noncanonical setup field value rejected"
  let short : Setup.Column := ⟨#[.affine 524287 0 0]⟩
  check (rejected ({artifact with range16 := short}.validate)) "truncated setup column rejected"
  let negative : Setup.Column := ⟨#[.affine 524288 0 (-1)]⟩
  check (rejected ({artifact with range16 := negative}.validate)) "negative setup progression rejected"
  let some region := artifact.tables[1]? | throw (IO.userError "missing setup table region")
  let wrongRegion := {region with offset := 2}
  check (rejected ({artifact with tables := artifact.tables.set! 1 wrongRegion}.validate))
    "wrong table region offset rejected"
  let .ok circuit := fromJson? (α := Circuit) (← match Json.parse importedCircuitSource with
    | .ok json => pure json
    | .error error => throw (IO.userError error))
    | throw (IO.userError "embedded setup circuit failed import")
  check (circuit.trace_len == artifact.circuit.trace_len &&
    circuit.generic_lookup_tables_width == 9) "embedded circuit retains exact setup geometry"
  for (setupPath, circuitPath) in [
      ("artifacts/setup/add-sub.json", "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"),
      ("artifacts/setup/bigint.json", "../../cs/compiled_circuits/bigint_with_extended_control_layout_no_caches_gkr.json")] do
    let .ok setup := Setup.parse (← IO.FS.readFile setupPath)
      | throw (IO.userError s!"native setup artifact failed import: {setupPath}")
    let .ok retained := Json.parse (← IO.FS.readFile circuitPath)
      | throw (IO.userError s!"retained circuit artifact failed import: {circuitPath}")
    check (toJson setup.circuit == retained) s!"{setupPath}: embedded circuit equals retained no-cache artifact"

end Tests.SetupImport
