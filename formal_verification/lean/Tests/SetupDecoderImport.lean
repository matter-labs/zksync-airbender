import Airbender.Data.Decoder.Setup.AddSub
import Airbender.Data.Decoder.Setup.JumpBranch
import Airbender.Data.Decoder.Setup.MulDiv
import Airbender.Data.Decoder.Setup.ShiftBinop
import Airbender.Data.Decoder.Setup.WordMemory
import Airbender.Data.Decoder.Setup.Subword
import Airbender.Data.Decoder.Setup.Unified
import Airbender.Import.SetupDecoderEmbed

namespace Tests.SetupDecoderImport
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

import_setup_decoder smokeDecoder from "artifacts/setup/decoder-smoke.json"

/-- error: setup artifact has no decoder table -/
#guard_msgs in
import_setup_decoder absentDecoder from "artifacts/setup/keccak.json"

theorem geometry : smokeDecoder.length = 4 ∧ smokeDecoderOffset = 8193 ∧
    smokeDecoderRealEnd = 8197 ∧ smokeDecoderTraceLength = 524288 ∧
    smokeDecoderPadding.length = 516091 := by decide +kernel

theorem physical_mask : smokeDecoderTagged = true ∧
    smokeDecoderColumnsMask = #[true, true, true, true, true, true, true, false, true] := by
  decide +kernel

theorem real_pc_zero : smokeDecoder.columns[0].get? 0 = some 0 ∧
    smokeDecoder.columns[8].get? 0 = some 46 := by decide +kernel

theorem unsupported_sentinel :
    smokeDecoder.columns[0].get? 2 = some (babyBearModulus - 1) := by decide +kernel

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then IO.println s!"PASS {message}"
  else throw (IO.userError s!"FAIL {message}")

private def checkPacked (path bytes : String) (packed : Trace.NativeDecoder.PackedSetup) : IO Unit := do
  let source ← IO.FS.readFile path
  let .ok artifact := Setup.parse source | throw (IO.userError s!"decoder setup failed import: {path}")
  check (source == bytes && packed.offset == artifact.circuit.offset_for_decoder_table &&
    packed.offset + packed.realRows.length + packed.padding.length == artifact.trace_len &&
    packed.width == artifact.columns.size &&
    packed.columnsMask == artifact.circuit.decode_table_columns_mask &&
    packed.tagged == artifact.circuit.tables_ids_in_generic_lookups)
    s!"{path}: exact decoder source, mask, prefix and complete physical domain"
  if packed.tagged then
    let some tags := artifact.columns[artifact.columns.size - 1]?
      | throw (IO.userError "tagged setup discriminator absent")
    check (Setup.Slices.matchesSource tags packed.prefixTags 0 packed.offset)
      s!"{path}: every fixed-prefix discriminator equals JSON"
  else
    check (packed.offset == 0 && packed.prefixTags.blocks.isEmpty)
      s!"{path}: decoder-only setup has no omitted prefix"
  check (artifact.columns.zipIdx.all fun (column, index) =>
    match packed.realRows.columns[index]?, packed.padding.columns[index]? with
    | some real, some padding =>
      Setup.Slices.matchesSource column real packed.offset packed.realRows.length &&
      Setup.Slices.matchesSource column padding (packed.offset + packed.realRows.length) packed.padding.length
    | _, _ => false)
    s!"{path}: every real decoder and committed-padding value equals JSON"

def run : IO Unit := do
  checkPacked "artifacts/setup/add-sub.json" Trace.NativeDecoder.addSubDecoderDataSourceBytes Trace.NativeDecoder.addSubSetup
  checkPacked "artifacts/setup/jump-branch.json" Trace.NativeDecoder.jumpBranchDecoderDataSourceBytes Trace.NativeDecoder.jumpBranchSetup
  checkPacked "artifacts/setup/mul-div.json" Trace.NativeDecoder.mulDivDecoderDataSourceBytes Trace.NativeDecoder.mulDivSetup
  checkPacked "artifacts/setup/shift-binop.json" Trace.NativeDecoder.shiftDecoderDataSourceBytes Trace.NativeDecoder.shiftBinopSetup
  checkPacked "artifacts/setup/word-memory.json" Trace.NativeDecoder.wordDecoderDataSourceBytes Trace.NativeDecoder.wordMemorySetup
  checkPacked "artifacts/setup/subword-memory.json" Trace.NativeDecoder.subwordDecoderDataSourceBytes Trace.NativeDecoder.subwordSetup
  checkPacked "artifacts/setup/unified.json" Trace.NativeDecoder.unifiedDecoderDataSourceBytes Trace.NativeDecoder.unifiedSetup
  let source ← IO.FS.readFile "artifacts/setup/decoder-smoke.json"
  let .ok setup := Setup.parse source | throw (IO.userError "decoder setup failed import")
  check (source == smokeDecoderSourceBytes &&
    setup.circuit.offset_for_decoder_table == smokeDecoderOffset &&
    setup.circuit.total_tables_size == smokeDecoderRealEnd &&
    setup.trace_len == smokeDecoderTraceLength &&
    setup.circuit.decode_table_columns_mask == smokeDecoderColumnsMask &&
    setup.circuit.tables_ids_in_generic_lookups == smokeDecoderTagged)
    "decoder: exact source, exported offsets, complete extent and physical mask"
  check (setup.columns.zipIdx.all fun (column, index) =>
    match smokeDecoder.columns[index]?, smokeDecoderPadding.columns[index]? with
    | some real, some padding =>
      Setup.Slices.matchesSource column real smokeDecoderOffset smokeDecoder.length &&
      Setup.Slices.matchesSource column padding smokeDecoderRealEnd smokeDecoderPadding.length
    | _, _ => false)
    "decoder: every real and committed-padding value equals parsed JSON"

end Tests.SetupDecoderImport
