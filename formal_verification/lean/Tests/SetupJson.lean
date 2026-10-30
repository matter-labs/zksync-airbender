import Airbender.Import.SetupJson
import Airbender.Import.Setup
open Lean
open Airbender.Import.SetupJson
namespace Tests.SetupJson
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem scalar_kernel : ((parse "{\"n\":37}").toOption.bind (fun j => (j.getObjVal? "n" >>= Json.getNat?).toOption)) = some 37 := by decide +kernel
theorem nested_kernel : ((parse "[true,false,null,\"abc\",-12,1.25e2]").toOption.map (fun j => j.getArr?.toOption.map Array.size)) = some (some 6) := by decide +kernel
theorem surrogate_kernel : ((parse "\"\\ud83d\\ude00\"").toOption.bind (fun j => j.getStr?.toOption)) = some "😀" := by decide +kernel
theorem lone_surrogate_kernel : ((parse "\"\\ud800x\"").toOption.bind (fun j => j.getStr?.toOption)) = some "�x" := by decide +kernel
theorem duplicate_key_kernel : ((parse "{\"n\":1,\"n\":2}").toOption.bind (fun j => (j.getObjVal? "n" >>= Json.getNat?).toOption)) = some 2 := by decide +kernel
theorem malformed_kernel : ((parse "[1,]").toOption.isNone && (parse "{\"n\":1,}").toOption.isNone && (parse "01").toOption.isNone && (parse "\"\\x\"").toOption.isNone) = true := by decide +kernel


/-- This block extends any earlier array prefix. Its size does not affect the proof. -/
theorem symbolic_array_block (earlier : List Json) :
    run (.ok { frames := [.array earlier], phase := .value false }) ['1', ',', '2', ','] =
      .ok { frames := [.array ([Json.num ⟨2, 0⟩, Json.num ⟨1, 0⟩] ++ earlier)], phase := .value false } := by
  rfl

private def compare (source : String) : IO Unit :=
  match Json.parse source, parse source with
  | .ok old, .ok new => unless old == new do throw <| IO.userError "JSON values differ"
  | .error _, .error _ => pure ()
  | _, _ => throw <| IO.userError "JSON acceptance differs"

#eval show IO Unit from do
  unless USize.size = 18446744073709551616 do
    throw <| IO.userError "JSON differential requires the supported 64-bit host"
  for source in ["{}", "[]", "0", "-0", "1234", "1.25e2", "-0.125E-2", "1e+01",
    "\"\\ud83d\\ude00\"", "\"\\ud800\"", "\"\\ud800x\"", "\"\\ud800\\udfff\"", "\"\\udfff\"",
    "\"\\u0000\"", "\"\\ud800\\u0000\"", "\"\\ud800\\uzzzz\"", "\"é😀\"",
    "{\"n\":1,\"n\":2}", "[true,false,null]", "\r\n\t [1,2] \t\r\n",
    "", "[", "{", "[1,]", "{\"n\":1,}", "01", "1e", "1.", "true false", "[1 2]",
    "\"\\x\"", "\"\n\"", "{1:2}", "[1,,2]"] do compare source
  IO.println "PASS setup JSON edge cases and kernel examples"
  let entries ← (System.FilePath.mk "artifacts/setup").readDir
  for entry in entries do
    unless entry.path.extension = some "json" do continue
    let source ← IO.FS.readFile entry.path
    compare source
    unless entry.fileName = "manifest.json" || entry.fileName = "native-evidence.json" do
      let oldJson ← match Json.parse source with
        | .ok value => pure value
        | .error error => throw <| IO.userError error
      let old : Airbender.Setup.Artifact ← match (fromJson? oldJson : Except String Airbender.Setup.Artifact) with
        | .ok value => pure value
        | .error error => throw <| IO.userError error
      let new ← match Airbender.Setup.parse source with
        | .ok value => pure value
        | .error error => throw <| IO.userError error
      unless old.version = new.version && old.field_modulus = new.field_modulus &&
          old.trace_len = new.trace_len && old.program = new.program && old.tables = new.tables &&
          old.columns = new.columns && old.range16 = new.range16 &&
          old.timestamp_range = new.timestamp_range && toJson old.circuit == toJson new.circuit do
        throw <| IO.userError s!"setup decoder changed imported data: {entry.path}"
    IO.println s!"PASS setup JSON differential {entry.fileName}"

end Tests.SetupJson
