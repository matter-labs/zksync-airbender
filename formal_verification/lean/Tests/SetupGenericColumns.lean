import Airbender.Data.Setup.Keccak.ThetaRhoGeneric
import Airbender.Data.Setup.Keccak.Chi5Generic
import Airbender.Import.SetupRegionEmbed

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

-- Check the value view against every original column, including physical padding.
#eval show IO Unit from do
  let .ok artifact := parse chi5GenericSourceBytes
    | throw (IO.userError "retained chi5 setup did not parse")
  unless artifact.columns.size == chi5Generic.columns.size do
    throw (IO.userError "shared chi5 import changed its physical width")
  for column in [:artifact.columns.size] do
    unless Slices.matchesSource ((artifact.columns[column]?).getD ⟨#[]⟩)
        ((chi5Generic.columns.toArray[column]?).getD ⟨#[]⟩) 0 artifact.trace_len do
      throw (IO.userError s!"shared chi5 import changed column {column}")
  unless decide (artifact.tables = chi5GenericRegions) do
    throw (IO.userError "shared chi5 import changed the native regions")

example : chi5GenericSourceBytes =
    include_str "../artifacts/setup/keccak-chi5.json" := by rfl

end Tests.SetupGenericColumns
