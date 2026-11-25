module
public import Proven.UnifiedReduced.Proth120.ArtifactChecks
public import Proven.Constraints

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120.Standard
set_option maxRecDepth 8192

/-- The standard-instruction proofs address ranges in their common order. The two additional
    quotient ranges are needed only by the modular instructions. -/
def importedConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :=
  let raw := Proth120.importedConstraints setup
  raw.take 124 ++ raw.drop 126

theorem holds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {env : Environment (ZMod p)}
    (h : FlatOperation.ConstraintsHoldFlat env (Proth120.importedConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat env (importedConstraints setup) := by
  apply Verification.holds_of_sublist h
  let raw := Proth120.importedConstraints setup
  change (raw.take 124 ++ raw.drop 126).Sublist raw
  have subset := (List.Sublist.refl (raw.take 124)).append
    (List.drop_sublist_drop_left raw (by decide : 124 ≤ 126))
  rwa [List.take_append_drop] at subset

end Airbender.UnifiedReduced.Proth120.Standard
