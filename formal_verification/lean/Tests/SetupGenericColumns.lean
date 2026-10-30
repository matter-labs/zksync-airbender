import Airbender.Data.Setup.Keccak.ThetaRhoGeneric

namespace Tests.SetupGenericColumns
open Airbender.Setup Airbender.Keccak.Split.Native.Fixed
set_option warningAsError true
set_option maxRecDepth 65536

-- Compare the complete parsed table at runtime. This test proves no proposition.
-- The controller row and tag theorems have separate kernel proofs.
#eval show IO Unit from do
  let .ok artifact := parse thetaRhoGenericSourceBytes
    | throw (IO.userError "retained theta/rho setup did not parse")
  unless decide (artifact.columns = thetaRhoGeneric.columns.toArray) do
    throw (IO.userError "shared column import changed a parsed block or value")
  unless decide (artifact.tables = thetaRhoGenericRegions) do
    throw (IO.userError "shared column import changed the native regions")
  unless artifact.tables.foldl (fun extent region =>
      max extent (region.offset + region.length)) 0 == thetaRhoGeneric.length do
    throw (IO.userError "shared column import changed the complete table extent")

example : thetaRhoGenericSourceBytes =
    include_str "../artifacts/setup/keccak-theta-rho.json" := by rfl

end Tests.SetupGenericColumns
