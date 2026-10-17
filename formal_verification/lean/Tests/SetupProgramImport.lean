import Airbender.Review.Helpers.Memory.NativeProgramData
import Airbender.Import.SetupRegionEmbed

namespace Tests.SetupProgramImport
open Airbender
set_option warningAsError true
set_option Elab.async false

/-- error: setup artifact has no selected program payload -/
#guard_msgs in
import_setup_program absentProgram from "artifacts/setup/keccak.json"

theorem geometry : Trace.ROM.nativeProgramData.image_words = 1048576 ∧
    Trace.ROM.nativeProgramData.text_words = 1048576 := by decide +kernel

theorem program_prefix : Trace.ROM.nativeProgramData.image.get? 0 = some 19 ∧
    Trace.ROM.nativeProgramData.image.get? 1 = some 4227219 ∧
    Trace.ROM.nativeProgramData.text.get? 2 = some 111 := by decide +kernel

theorem padding : Trace.ROM.nativeProgramData.image.get? 1048575 = some 0 ∧
    Trace.ROM.nativeProgramData.text.get? 1048575 = some 0 := by decide +kernel

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then IO.println s!"PASS {message}"
  else throw (IO.userError s!"FAIL {message}")

def run : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/word-memory.json"
  let .ok setup := Setup.parse source | throw (IO.userError "program setup failed import")
  let some program := setup.program | throw (IO.userError "program payload is absent")
  let imported := Trace.ROM.nativeProgramData
  check (source == Trace.ROM.nativeProgramDataSourceBytes &&
    imported.image_words == program.image_words && imported.text_words == program.text_words)
    "selected program: exact source bytes and image/text geometry"
  check (Setup.Slices.matchesSource program.image imported.image 0 program.image_words &&
    Setup.Slices.matchesSource program.text imported.text 0 program.text_words)
    "selected program: every image/text word and padding value equals JSON"

end Tests.SetupProgramImport
