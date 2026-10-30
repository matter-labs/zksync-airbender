import Airbender.Data.Setup.Keccak.ThetaRhoPhysical
import Airbender.Import.Setup

namespace Tests.SetupThetaGeneric
open Airbender Airbender.Setup Airbender.Keccak.Split.Native.Fixed
set_option maxRecDepth 65536

/-- Compare every physical source cell with the composed native generic view. -/
def matchesSource (artifact : Artifact) : Bool := Id.run do
  unless artifact.trace_len = thetaRhoPhysicalGenericLength && artifact.columns.size = 9 do return false
  let mut blocks : Array Nat := Array.replicate 9 0
  let mut positions : Array Nat := Array.replicate 9 0
  for h : row in [:thetaRhoPhysicalGenericLength] do
    let expected := thetaRhoPhysicalGenericRow ⟨row, by exact h.2.1⟩
    for column in [:9] do
      let some original := artifact.columns[column]? | return false
      let some block := original.blocks[blocks[column]!]? | return false
      let some value := block.get? positions[column]! | return false
      let some actual := expected.toArray[column]? | return false
      unless actual = signedValue value do return false
      positions := positions.set! column (positions[column]! + 1)
      if positions[column]! = block.length then
        positions := positions.set! column 0
        blocks := blocks.set! column (blocks[column]! + 1)
  for column in [:9] do
    let some original := artifact.columns[column]? | return false
    unless blocks[column]! = original.blocks.size && positions[column]! = 0 do return false
  return true

#eval do
  let source ← IO.FS.readFile "artifacts/setup/keccak-theta-rho.json"
  unless source = thetaRhoXorSourceBytes && source = thetaRhoSlotsSourceBytes &&
      source = thetaRhoControlSourceBytes && source = thetaRhoXorSplitSourceBytes do
    throw (IO.userError "native theta/rho setup source changed after its views were imported")
  let artifact ← match Setup.parse source with
    | .ok artifact => pure artifact
    | .error error => throw (IO.userError error)
  unless matchesSource artifact do
    throw (IO.userError "complete native theta/rho setup view differs from its source")
  IO.println "PASS complete native theta/rho setup: 4194304 rows, 9 physical columns"

end Tests.SetupThetaGeneric
