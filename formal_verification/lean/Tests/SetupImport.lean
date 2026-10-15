import Airbender.Import.SetupEmbed

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

def run : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/decoder-smoke.json"
  check (source == importedSourceBytes) "setup source bytes equal embedded artifact"
  let .ok artifact := Setup.parse source | throw (IO.userError "setup artifact failed import")
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
