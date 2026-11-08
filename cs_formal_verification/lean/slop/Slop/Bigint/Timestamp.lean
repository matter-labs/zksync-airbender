module
public import Human.Circuits.Bigint.Artifact
public import Slop.Bigint.ArtifactChecks
public import Slop.Delegation.ClockFacts
public import Slop.Bigint.Shapes

@[expose] public section

namespace Airbender.Bigint.Proofs
open Trace
set_option warningAsError true

/-- Lookups `1 + 2 i` and `2 + 2 i` of the timestamp list: the two limb comparisons of port `i`. -/
private abbrev lowerExpr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  Shapes.sumFrom (Shapes.constant (Int.ofNat 0)) [Shapes.constant (Int.negSucc 1),
    Shapes.product (Shapes.constant (Int.negSucc 0)) (Shapes.cell 1),
    Shapes.product (Shapes.constant (Int.ofNat 1)) (Shapes.cell (216 + 3 * i)),
    Shapes.product (Shapes.constant (Int.ofNat 524288)) (Shapes.cell (218 + 3 * i))]

private abbrev upperExpr {p : Nat} (i : Nat) : Expression (ZMod p) :=
  Shapes.sumFrom (Shapes.constant (Int.ofNat 0)) [Shapes.constant (Int.ofNat 524288),
    Shapes.product (Shapes.constant (Int.negSucc 0)) (Shapes.cell 2),
    Shapes.product (Shapes.constant (Int.ofNat 1)) (Shapes.cell (217 + 3 * i)),
    Shapes.product (Shapes.constant (Int.negSucc 0)) (Shapes.cell (218 + 3 * i))]

private theorem clock_shapes {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) (i : Fin 19) :
    (FlatOperation.constraints (importedConstraints setup)).get
        ⟨116 + i.val, by rw [constraint_count]; omega⟩ = Shapes.flag (218 + 3 * i.val) ∧
      (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).get
        ⟨1 + 2 * i.val, by rw [timestamp_count]; omega⟩ = timestampLookup (lowerExpr i.val) ∧
      (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).get
        ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩ = timestampLookup (upperExpr i.val) := by
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
    obtain ⟨bitShape, lowerShape, upperShape⟩ := clock_shapes setup i
    have bit := Shapes.flag_bit core bitShape
    have lower := Verification.lookup_of_holds timestamps
      ⟨1 + 2 * i.val, by rw [timestamp_count]; omega⟩
    have upper := Verification.lookup_of_holds timestamps
      ⟨2 + 2 * i.val, by rw [timestamp_count]; omega⟩
    rw [lowerShape] at lower
    rw [upperShape] at upper
    replace lower := Trace.Proofs.range_bound lower
    replace upper := Trace.Proofs.range_bound upper
    simp only [List.foldl, Expression.eval, Verification.environment] at lower upper
    push_cast at lower upper
    have invocation : importedConstraintsDelegationColumns.invocation = #v[1, 2] := by
      rw [delegation_columns]
    simp only [invocation, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    refine ⟨?_, ?_, ?_⟩
    · rcases bit with zero | one
      · rw [zero, zero_mul]
      · rw [one, sub_self, mul_zero]
    · convert lower using 2
      simp only [Trace.timestampBase]
      push_cast
      ring
    · convert upper using 2
      simp only [Trace.timestampBase]
      push_cast
      ring

end Airbender.Bigint.Proofs
