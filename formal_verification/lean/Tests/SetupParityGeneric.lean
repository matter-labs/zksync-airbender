import Airbender.Data.Setup.Keccak.ColumnParityGeneric
import Airbender.Import.Setup

namespace Tests.SetupParityGeneric
open Airbender Airbender.Setup Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/-- Compare every physical source cell with the composed native generic view. -/
def matchesSource (artifact : Artifact) : Bool := Id.run do
  unless artifact.trace_len = columnParityGenericLength && artifact.columns.size = 8 do return false
  let mut blocks : Array Nat := Array.replicate 8 0
  let mut positions : Array Nat := Array.replicate 8 0
  for h : row in [:columnParityGenericLength] do
    let expected := columnParityGenericRow ⟨row, by exact h.2.1⟩
    for column in [:8] do
      let some original := artifact.columns[column]? | return false
      let some block := original.blocks[blocks[column]!]? | return false
      let some value := block.get? positions[column]! | return false
      let some actual := expected.toArray[column]? | return false
      unless actual = signedValue value do return false
      positions := positions.set! column (positions[column]! + 1)
      if positions[column]! = block.length then
        positions := positions.set! column 0
        blocks := blocks.set! column (blocks[column]! + 1)
  for column in [:8] do
    let some original := artifact.columns[column]? | return false
    unless blocks[column]! = original.blocks.size && positions[column]! = 0 do return false
  return true

#eval do
  let source ← IO.FS.readFile "artifacts/setup/keccak-column-parity.json"
  unless source = columnParityIotaSourceBytes && source = columnParitySlotsSourceBytes &&
      source = columnParityControlSourceBytes && source = columnParityXor5SourceBytes do
    throw (IO.userError "native parity setup source changed after its views were imported")
  let artifact ← match Setup.parse source with
    | .ok artifact => pure artifact
    | .error error => throw (IO.userError error)
  unless matchesSource artifact do
    throw (IO.userError "complete native parity setup view differs from its source")
  IO.println "PASS complete native parity setup: 4194304 rows, 8 physical columns"

end Tests.SetupParityGeneric
