import Airbender.Import.Parse
import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5
import Airbender.Review.Circuits.Keccak.SplitColumnParityCached
import Airbender.Review.Circuits.Keccak.SplitThetaRhoCached
import Airbender.Review.Circuits.Keccak.SplitChi5Cached

namespace Tests.SplitKeccakImport
open Airbender Airbender.Keccak.Split

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected {α : Type} : Except String α → Bool
  | .ok _ => false
  | .error _ => true

private def load (name : String) (cached : Bool) : IO (Airbender.Circuit × String) := do
  let source ← IO.FS.readFile
    s!"../../cs/compiled_circuits/keccak_{name}_layout{if cached then "" else "_no_caches"}_gkr.json"
  match Airbender.parseCircuit source with
  | .ok circuit => pure (circuit, source)
  | .error reason => throw (IO.userError reason)

/-- Check all six source-byte bindings and reject malformed split lookup and
group metadata. This exercises the importer guards; no worker effect is proved. -/
def run : IO Unit := do
  let (parity, paritySource) ← load "column_parity" false
  let (theta, thetaSource) ← load "theta_rho" false
  let (chi, chiSource) ← load "chi5" false
  let (parityCached, parityCachedSource) ← load "column_parity" true
  let (thetaCached, thetaCachedSource) ← load "theta_rho" true
  let (chiCached, chiCachedSource) ← load "chi5" true
  require (paritySource == ColumnParity.importedConstraintsSourceBytes)
    "column parity source bytes changed"
  require (thetaSource == ThetaRho.importedConstraintsSourceBytes)
    "theta/rho source bytes changed"
  require (chiSource == Chi5.importedConstraintsSourceBytes)
    "chi5 source bytes changed"
  require (parityCachedSource == ColumnParityCached.importedConstraintsSourceBytes)
    "cached column parity source bytes changed"
  require (thetaCachedSource == ThetaRhoCached.importedConstraintsSourceBytes)
    "cached theta/rho source bytes changed"
  require (chiCachedSource == Chi5Cached.importedConstraintsSourceBytes)
    "cached chi5 source bytes changed"
  let .ok parityQueries := parity.keccakColumnParityQueries |
    throw (IO.userError "column parity query profile rejected")
  let .ok thetaQueries := theta.keccakThetaRhoQueries |
    throw (IO.userError "theta/rho query profile rejected")
  let .ok chiQueries := chi.keccakChi5Queries |
    throw (IO.userError "chi5 query profile rejected")
  let .ok parityCachedQueries := parityCached.keccakColumnParityQueries |
    throw (IO.userError "cached column parity query profile rejected")
  let .ok thetaCachedQueries := thetaCached.keccakThetaRhoQueries |
    throw (IO.userError "cached theta/rho query profile rejected")
  let .ok chiCachedQueries := chiCached.keccakChi5Queries |
    throw (IO.userError "cached chi5 query profile rejected")
  require (parityQueries.size == 22 && thetaQueries.size == 50 &&
    chiQueries.size == 17 && parityCachedQueries.size == 22 &&
    thetaCachedQueries.size == 50 && chiCachedQueries.size == 17)
    "split lookup counts changed"
  let .ok thetaGroups := theta.splitTimestampGroups |
    throw (IO.userError "theta/rho timestamp groups rejected")
  let .ok chiGroups := chi.splitTimestampGroups |
    throw (IO.userError "chi5 timestamp groups rejected")
  let .ok thetaCachedGroups := thetaCached.splitTimestampGroups |
    throw (IO.userError "cached theta/rho timestamp groups rejected")
  let .ok chiCachedGroups := chiCached.splitTimestampGroups |
    throw (IO.userError "cached chi5 timestamp groups rejected")
  require (thetaGroups.size == 4 && chiGroups.size == 6 &&
    thetaCachedGroups.size == 4 && chiCachedGroups.size == 6)
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
