module
public import Human.Circuits.Blake2G.Model
public import Slop.Constraints
public import Mathlib.Tactic.FinCases
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Blake2G.Proofs

/-- The twenty arithmetic assertions and eighteen XOR queries, selected from
    the imported artifact itself. Controller, addresses and timestamps are absent. -/
def mixingConstraints {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    List (FlatOperation (ZMod p)) :=
  ((importedConstraints setup).drop 3).take 20 ++ (importedConstraints setup).drop 35

theorem mixing_constraint_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.constraints (mixingConstraints setup)).length = 20 := by rfl

theorem mixing_lookup_count {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 9)) :
    (FlatOperation.lookups (mixingConstraints setup)).length = 18 := by rfl

theorem mixing_holds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (mixingConstraints setup) := by
  apply Verification.holds_append
  · exact Verification.holds_of_sublist h
      ((List.take_sublist 20 _).trans (List.drop_sublist 3 _))
  · exact Verification.holds_of_sublist h (List.drop_sublist 35 _)

def mixingModel {p : Nat} [Fact p.Prime] (control : Fin 512 → Vector Nat 7) :
    Verification.CircuitModel Input Words (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (mixingConstraints (setupTable control))
  represents := WordMapping

end Airbender.Blake2G.Proofs
