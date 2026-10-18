import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Tables.PhysicalSetup

namespace Airbender.Verification.NativeSetup

import_native_scalars scalars from "artifacts/setup/scalars-native.json"

/-- The two shared native scalar columns, at checked compiled positions 0/1. -/
inductive ScalarKind where
  | range16
  | timestamp19
  deriving DecidableEq

def ScalarKind.bits : ScalarKind → Nat
  | .range16 => 16
  | .timestamp19 => 19

def ScalarKind.data : ScalarKind → Setup.TableData 1
  | .range16 => scalarsRange16
  | .timestamp19 => scalarsTimestamp19

/-- Source-shaped active scalar rows: actual exported prefix, then zero fill.
    The final normalization row is excluded by Row; Rust physical trace/LDE
    refinement is separate from this model and literal prefix certificate. -/
def scalarRow {p : Nat} (kind : ScalarKind) (row : Row) : ZMod p :=
  if h : row.val < kind.data.length then (kind.data.row ⟨row.val, h⟩)[0] else 0

def ScalarContains {p : Nat} (kind : ScalarKind) (value : ZMod p) : Prop :=
  ∃ row : Row, scalarRow kind row = value

end Airbender.Verification.NativeSetup
