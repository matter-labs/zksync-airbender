module
public import Human.Circuits.Bigint.Artifact
public import Slop.Bigint.ArtifactChecks
public import Slop.Delegation.ClockShapes
public import Slop.Bigint.Shapes
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.Bigint.Proofs
open Trace
set_option warningAsError true

/-- Constraint `116 + i` and lookups `1 + 2 i`, `2 + 2 i` of the timestamp list: the borrow flag and
    the two limb comparisons of port `i`. -/
private theorem clock_shapes {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3))
    (i : Fin 19) :
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨116 + i.val, by rw [constraint_count]; omega⟩ = Templates.flag (218 + 3 * i.val) ∧
      (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).get
        ⟨1 + 2 * i.val, by rw [timestamp_count]; omega⟩ =
          timestampLookup (Delegation.Proofs.clockLower (216 + 3 * i.val) (218 + 3 * i.val)) ∧
      (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).get
        ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩ =
          timestampLookup (Delegation.Proofs.clockUpper (217 + 3 * i.val) (218 + 3 * i.val)) := by
  refine ⟨?_, ?_, ?_⟩ <;> fin_cases i <;> op_index <;> rfl

theorem clock_facts {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 3)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    Delegation.Proofs.ClockFacts importedConstraintsDelegationColumns w := by
  have core := Verification.holds_of_sublist h
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have timestamps := Verification.holds_of_sublist h
    (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  refine ⟨?_, ?_⟩
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    change (2 : Nat) < 4
    decide
  · intro port member
    rw [delegation_columns] at member
    simp only [Vector.toArray_ofFn, Array.mem_ofFn] at member
    obtain ⟨i, rfl⟩ := member
    obtain ⟨bit, lower, upper⟩ := clock_shapes setup i
    exact Delegation.Proofs.port_comparison core timestamps (by rw [delegation_columns]) _ rfl
      bit lower upper

end Airbender.Bigint.Proofs
