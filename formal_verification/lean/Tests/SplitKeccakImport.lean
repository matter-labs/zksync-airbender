import Airbender.Import.Parse
import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5

namespace Tests.SplitKeccakImport
open Airbender Airbender.Keccak.Split

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} : Except String α → Bool
  | .ok _ => false
  | .error _ => true

private def load (name : String) : IO Airbender.Circuit := do
  let source ← IO.FS.readFile
    s!"../../cs/compiled_circuits/keccak_{name}_layout_no_caches_gkr.json"
  match Airbender.parseCircuit source with
  | .ok circuit => pure circuit
  | .error reason => throw (IO.userError reason)

/-- Check the three source-byte bindings and reject malformed split lookup and
group metadata. This exercises the importer guards; no worker effect is proved. -/
def run : IO Unit := do
  let parity ← load "column_parity"
  let theta ← load "theta_rho"
  let chi ← load "chi5"
  let paritySource ← IO.FS.readFile
    "../../cs/compiled_circuits/keccak_column_parity_layout_no_caches_gkr.json"
  let thetaSource ← IO.FS.readFile
    "../../cs/compiled_circuits/keccak_theta_rho_layout_no_caches_gkr.json"
  let chiSource ← IO.FS.readFile
    "../../cs/compiled_circuits/keccak_chi5_layout_no_caches_gkr.json"
  require (paritySource == ColumnParity.importedConstraintsSourceBytes)
    "column parity source bytes changed"
  require (thetaSource == ThetaRho.importedConstraintsSourceBytes)
    "theta/rho source bytes changed"
  require (chiSource == Chi5.importedConstraintsSourceBytes)
    "chi5 source bytes changed"
  let .ok parityQueries := parity.keccakColumnParityQueries |
    throw (IO.userError "column parity query profile rejected")
  let .ok thetaQueries := theta.keccakThetaRhoQueries |
    throw (IO.userError "theta/rho query profile rejected")
  let .ok chiQueries := chi.keccakChi5Queries |
    throw (IO.userError "chi5 query profile rejected")
  require (parityQueries.size == 22 && thetaQueries.size == 50 &&
    chiQueries.size == 17) "split lookup counts changed"
  let .ok thetaGroups := theta.splitTimestampGroups |
    throw (IO.userError "theta/rho timestamp groups rejected")
  let .ok chiGroups := chi.splitTimestampGroups |
    throw (IO.userError "chi5 timestamp groups rejected")
  require (thetaGroups.size == 4 && chiGroups.size == 6)
    "split timestamp group counts changed"
  let wrongTheta : Airbender.Circuit :=
    {theta with generic_lookup_tables_width := 8}
  require (rejected wrongTheta.keccakThetaRhoQueries)
    "wrong theta/rho lookup width accepted"
  let missingGroups : Airbender.Circuit :=
    {chi with aux_layout_data :=
      {chi.aux_layout_data with relative_timestamp_groups := some #[]}}
  require (rejected missingGroups.splitTimestampGroups)
    "missing chi5 timestamp groups accepted"

#eval run

end Tests.SplitKeccakImport
