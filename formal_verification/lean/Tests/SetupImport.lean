import Airbender.Data.Setup.UnifiedReduced.NativeFixedData
import Airbender.Data.Setup.UnifiedReduced.Native.ROMData
import Airbender.Data.Setup.WordMemory.ZeroData
import Airbender.Data.Setup.WordMemory.ROMData
import Airbender.Data.Tables.SubwordROMData
import Airbender.Import.SetupEmbed
import Airbender.Import.NativeJson
import Airbender.Data.Setup.Keccak.FixedData
import Airbender.Data.Setup.Keccak.RotationTemplates
import Airbender.Review.Circuits.Bigint.Tables.Setup
import Airbender.Data.Setup.Blake2G.Controller
import Airbender.Data.Setup.Keccak.Controller
import Airbender.Data.Setup.Blake2G.XorData
import Airbender.Data.Setup.Blake2Round.XorData
import Airbender.Review.Helpers.Tables.PairData
import Tests.SetupRegionImport
import Airbender.Data.Tables.ShiftData
import Airbender.Data.Tables.SubwordData

namespace Tests.SetupImport
open Airbender Lean

import_setup imported from "artifacts/setup/decoder-smoke.json"

/-- error: setup template column is absent -/
#guard_msgs in
import_setup_templates absentColumn from "artifacts/setup/keccak.json"
  native_table_id 40 physical_column 999 row_offsets [393216]

/-- error: setup template offset is outside its native region -/
#guard_msgs in
import_setup_templates outsideRegion from "artifacts/setup/keccak.json"
  native_table_id 40 physical_column 2 row_offsets [1048576]

/-- error: setup template offset is not a stored block boundary -/
#guard_msgs in
import_setup_templates insideBlock from "artifacts/setup/keccak.json"
  native_table_id 40 physical_column 2 row_offsets [393217]

/-- error: setup template block is not periodic -/
#guard_msgs in
import_setup_templates affineBlock from "artifacts/setup/keccak.json"
  native_table_id 40 physical_column 2 row_offsets [0]

def absentLiteral : Array Nat := #[999999999]

/-- error: shared setup literal Tests.SetupImport.absentLiteral is absent from imported data -/
#guard_msgs in
share_setup_literals absentSharedLiteral from Keccak.zeroData using [absentLiteral]

/-- error: shared setup literal must be an Array Nat definition -/
#guard_msgs in
share_setup_literals wrongLiteralType from Keccak.zeroData using [Keccak.rotationTemplatesColumn]

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

private def checkRegions {count : Nat} (label source : String) (artifact : Setup.Artifact)
    (data : Fin count → Setup.TableData width) (regions : Fin count → Setup.Region)
    (sources : Vector String count) : IO Unit := do
  for k in List.finRange count do
    let imported := data k
    let region := regions k
    check (sources[k] == source && artifact.tables.contains region &&
      imported.length == region.length && imported.offset == 0 &&
      imported.columns.size == artifact.columns.size)
      s!"{label} region {region.id}: exact source, metadata and physical geometry"
    check (imported.columns.toArray.zipIdx.all fun (column, index) =>
      match artifact.columns[index]? with
      | some original => Setup.Slices.matchesSource original column region.offset region.length
      | none => false)
      s!"{label} region {region.id}: every key, output, padding and tag equals JSON"

def run : IO Unit := do
  let jumpSource ← IO.FS.readFile "artifacts/setup/jump-branch.json"
  let .ok jump := Setup.parse jumpSource
    | throw (IO.userError "jump/branch setup artifact failed import")
  let jumpData : Vector (Setup.TableData 10) 4 :=
    #v[Verification.regZeroData, Verification.signData,
      Verification.jumpCleanupData, Verification.conditionalData]
  let jumpRegions : Vector Setup.Region 4 :=
    #v[Verification.regZeroDataRegion, Verification.signDataRegion,
      Verification.jumpCleanupDataRegion, Verification.conditionalDataRegion]
  checkRegions "jump/branch fixed" jumpSource jump (fun k => jumpData[k])
    (fun k => jumpRegions[k])
    #v[Verification.regZeroDataSourceBytes, Verification.signDataSourceBytes,
      Verification.jumpCleanupDataSourceBytes, Verification.conditionalDataSourceBytes]
  let mulSource ← IO.FS.readFile "artifacts/setup/mul-div.json"
  let .ok mulSetup := Setup.parse mulSource
    | throw (IO.userError "mul/div setup artifact failed import")
  checkRegions "mul/div low-byte" mulSource mulSetup
    (fun (_ : Fin 1) => Verification.lowByteData)
    (fun _ => Verification.lowByteDataRegion) #v[Verification.lowByteDataSourceBytes]
  let shiftSource ← IO.FS.readFile "artifacts/setup/shift-binop.json"
  let .ok shiftSetup := Setup.parse shiftSource
    | throw (IO.userError "shift/binop setup artifact failed import")
  checkRegions "shift/binop fixed" shiftSource shiftSetup Verification.shiftData Verification.shiftRegion
    #v[Verification.byteZeroDataSourceBytes, Verification.byteSignDataSourceBytes,
      Verification.byteXorDataSourceBytes, Verification.byteOrDataSourceBytes,
      Verification.byteAndDataSourceBytes, Verification.byteTruncateDataSourceBytes,
      Verification.byteShiftDataSourceBytes]
  let subwordSource ← IO.FS.readFile "artifacts/setup/subword-memory.json"
  let .ok subwordSetup := Setup.parse subwordSource
    | throw (IO.userError "subword setup artifact failed import")
  checkRegions "subword disabled" subwordSource subwordSetup
    (fun (_ : Fin 1) => Verification.subwordZeroData)
    (fun _ => Verification.subwordZeroDataRegion) #v[Verification.subwordZeroDataSourceBytes]
  checkRegions "subword fixed" subwordSource subwordSetup
    Verification.subwordFixedData Verification.subwordFixedRegion
    #v[Verification.storePlaceDataSourceBytes, Verification.storeClearDataSourceBytes,
      Verification.loadHalfDataSourceBytes, Verification.loadByteDataSourceBytes]
  checkRegions "subword ROM" subwordSource subwordSetup
    (fun k : Fin 2 => Verification.subwordROMData (k.val == 1))
    (fun k => Verification.subwordROMRegion (k.val == 1))
    #v[Verification.subwordROMHalfDataSourceBytes, Verification.subwordROMByteDataSourceBytes]
  let wordSource ← IO.FS.readFile "artifacts/setup/word-memory.json"
  let .ok wordSetup := Setup.parse wordSource
    | throw (IO.userError "word-memory setup artifact failed import")
  let wordData : Vector (Setup.TableData 9) 2 := #v[Trace.ROM.nativeWordZeroData, Trace.ROM.nativeWordData]
  let wordRegions : Vector Setup.Region 2 := #v[Trace.ROM.nativeWordZeroDataRegion, Trace.ROM.nativeWordDataRegion]
  checkRegions "word ROM" wordSource wordSetup (fun k => wordData[k]) (fun k => wordRegions[k])
    #v[Trace.ROM.nativeWordZeroDataSourceBytes, Trace.ROM.nativeWordDataSourceBytes]
  let unifiedSource ← IO.FS.readFile "artifacts/setup/unified.json"
  let .ok unifiedSetup := Setup.parse unifiedSource
    | throw (IO.userError "unified setup artifact failed import")
  checkRegions "unified fixed" unifiedSource unifiedSetup
    UnifiedReduced.Setup.nativeFixedData UnifiedReduced.Setup.nativeFixedRegion
    #v[UnifiedReduced.Setup.nativeZeroDataSourceBytes, UnifiedReduced.Setup.nativeByteSignDataSourceBytes,
      UnifiedReduced.Setup.nativeXorDataSourceBytes, UnifiedReduced.Setup.nativeOrDataSourceBytes,
      UnifiedReduced.Setup.nativeAndDataSourceBytes, UnifiedReduced.Setup.nativeTruncationDataSourceBytes,
      UnifiedReduced.Setup.nativeShiftDataSourceBytes, UnifiedReduced.Setup.nativeRegisterZeroDataSourceBytes,
      UnifiedReduced.Setup.nativeSignDataSourceBytes, UnifiedReduced.Setup.nativeCleanupDataSourceBytes,
      UnifiedReduced.Setup.nativeConditionalDataSourceBytes, UnifiedReduced.Setup.nativeRotate16DataSourceBytes,
      UnifiedReduced.Setup.nativeRotate12DataSourceBytes, UnifiedReduced.Setup.nativeRotate8DataSourceBytes,
      UnifiedReduced.Setup.nativeRotate7DataSourceBytes]
  checkRegions "unified ROM" unifiedSource unifiedSetup
    (fun _ : Fin 1 => UnifiedReduced.Setup.nativeROMData)
    (fun _ => UnifiedReduced.Setup.nativeROMDataRegion) #v[UnifiedReduced.Setup.nativeROMDataSourceBytes]
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
  checkRegions "BLAKE2 G" controllerSource controllerSetup Blake2G.xorData Blake2G.xorRegion
    #v[Blake2G.xor8DataSourceBytes, Blake2G.xor3DataSourceBytes,
      Blake2G.xor4DataSourceBytes, Blake2G.xor7DataSourceBytes, Blake2G.xor9DataSourceBytes]
  let roundSource ← IO.FS.readFile "artifacts/setup/blake-round.json"
  let .ok roundSetup := Setup.parse roundSource
    | throw (IO.userError "extended BLAKE setup artifact failed import")
  checkRegions "extended BLAKE" roundSource roundSetup Blake2Round.xorData Blake2Round.xorRegion
    #v[Blake2Round.xor8DataSourceBytes, Blake2Round.xor7DataSourceBytes,
      Blake2Round.xor9DataSourceBytes, Blake2Round.xor8CarryDataSourceBytes,
      Blake2Round.xor7CarryDataSourceBytes, Blake2Round.xor4x3DataSourceBytes]
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
  checkRegions "Keccak fixed" keccakSource keccakSetup Keccak.fixedData Keccak.fixedRegion
    #v[Keccak.zeroDataSourceBytes, Keccak.xorDataSourceBytes,
      Keccak.iotaDataSourceBytes, Keccak.chiDataSourceBytes, Keccak.rotationDataSourceBytes]
  let templates : Vector (Array Nat) 10 :=
    #v[Keccak.rotationTemplates0, Keccak.rotationTemplates1, Keccak.rotationTemplates2,
      Keccak.rotationTemplates3, Keccak.rotationTemplates4, Keccak.rotationTemplates5,
      Keccak.rotationTemplates6, Keccak.rotationTemplates7, Keccak.rotationTemplates8,
      Keccak.rotationTemplates9]
  check (Keccak.rotationTemplatesSourceBytes == keccakSource &&
    keccakSetup.tables.contains Keccak.rotationTemplatesRegion &&
    Keccak.rotationTemplatesRegion.id == 40 && Keccak.rotationTemplatesColumn == 2 &&
    Keccak.rotationTemplatesRowOffsets.size == 10 &&
    Keccak.rotationTemplatesRepetitions.size == 10 && Keccak.rotationTemplatesStrides.size == 10)
    "Keccak stored templates retain exact source and native region metadata"
  for k in List.finRange 10 do
    let start := Keccak.rotationTemplatesRegion.offset + Keccak.rotationTemplatesRowOffsets[k.val]!
    check ((templates[k].zipIdx).all fun (value, index) =>
      keccakSetup.columns[Keccak.rotationTemplatesColumn]?.bind (fun column =>
        column.get? (start + index)) == some value)
      s!"Keccak stored template {k.val}: every value equals the parsed physical rows"
    let some physical := keccakSetup.columns[Keccak.rotationTemplatesColumn]?
      | throw (IO.userError "Keccak stored-template column absent")
    let (_, selected) := physical.blocks.foldl (fun (position, found) block =>
      (position + block.length, if position == start then some block else found))
      ((0 : Nat), (none : Option Setup.Block))
    let some (.periodic count stride original) := selected
      | throw (IO.userError "Keccak stored-template native block absent")
    check (templates[k] == original &&
      Keccak.rotationTemplatesRepetitions[k.val]? == some count &&
      Keccak.rotationTemplatesStrides[k.val]? == some stride)
      s!"Keccak stored template {k.val}: native stored values, count and stride preserved"
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
    check (setup.circuit.toNativeJson == retained)
      s!"{setupPath}: embedded circuit equals retained no-cache artifact"
    for value in [0, 2013265920] do
      let .ok padding := fromJson? (α := Coefficient) (toJson value)
        | throw (IO.userError "padding coefficient failed import")
      let present := {setup.circuit with generic_lookup_padding := some padding}
      check ((present.toNativeJson.getObjVal? "generic_lookup_padding").toOption == some (toJson value))
        s!"native circuit serialization retains present padding {value}"
    let absent := {setup.circuit with generic_lookup_padding := none}
    check (rejected (absent.toNativeJson.getObjVal? "generic_lookup_padding"))
      "native circuit serialization omits absent padding"
    check ((absent.toNativeJson.getObjVal? "_marker").toOption == some Json.null)
      "native circuit serialization retains other explicit null fields"

end Tests.SetupImport
