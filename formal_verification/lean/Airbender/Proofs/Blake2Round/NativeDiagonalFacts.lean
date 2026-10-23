import Airbender.Proofs.Blake2Round.NativeBooleanBindings
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeDiagonalAssignment
import Airbender.Proofs.Blake2Round.NativeXorTransfer
import Airbender.Proofs.Blake2G.QueryCarries
import Airbender.Proofs.Blake2Round.NativeDiagonalView0
import Airbender.Proofs.Blake2Round.NativeDiagonalView1
import Airbender.Proofs.Blake2Round.NativeDiagonalView2
import Airbender.Proofs.Blake2Round.NativeDiagonalView3


namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private theorem carry_values_bound {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.AtLeast p 512) (kind : Fin 2)
    {source : Vector (Expression (ZMod p)) 6} {values : Vector (ZMod p) 6}
    {env : Environment (ZMod p)} (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (evaluated : source.map (Expression.eval env) = values)
    (selected : values[5] = ((carryTags[kind] : Nat) : ZMod p)) : values[2].val < 3 := by
  have tag := congrArg (fun row : Vector (ZMod p) 6 => row[5]) evaluated
  have value := congrArg (fun row : Vector (ZMod p) 6 => row[2]) evaluated
  simp only [Vector.getElem_map] at tag value
  have bound := carry_value_bound hp kind member (tag.trans selected)
  rw [value] at bound
  exact bound


private theorem checked_diagonal_frame {p : Nat} [Fact p.Prime]
    (call : Fin 4) (w : Nat → ZMod p) : diagonalFrame call w =
      #v[NativeDiagonalView0.frame w, NativeDiagonalView1.frame w,
        NativeDiagonalView2.frame w, NativeDiagonalView3.frame w][call] := by
  fin_cases call
  · exact NativeDiagonalView0.frame_eq w
  · exact NativeDiagonalView1.frame_eq w
  · exact NativeDiagonalView2.frame_eq w
  · exact NativeDiagonalView3.frame_eq w

local macro "carry_from_view " member:ident " using " hp:term ", " binding:term ", " evaluated:term ", " values:ident ", " frame:ident ", " kind:term : tactic =>
  `(tactic| (
    have membership := $member
    simp only [NativeLayout.additionCarryQueries, NativeLayout.finalCarryQueries,
      Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ] at membership
    have normalizedBinding := $binding
    norm_num [NativeLayout.queryIndex] at normalizedBinding membership
    rw [normalizedBinding] at membership
    have bound := carry_values_bound $hp $kind membership $evaluated (by
      unfold $values:ident
      norm_num [carryTags])
    rw [checked_diagonal_frame]
    unfold $values:ident at bound
    simp only [Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    unfold $frame:ident
    simpa using bound))

/-- All four addition carries are supplied by native carry-aware memberships. -/
theorem native_diagonal_addition_carries {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 4) :
    (diagonalFrame call w).addCarries[slot].val < 3 := by
  have source := Verification.lookup_of_holds h
    ⟨NativeLayout.queryIndex .diagonal call NativeLayout.additionCarryQueries[slot], by
      rw [lookup_count]; have := call.isLt
      have := NativeLayout.additionCarryQueries[slot].isLt
      dsimp [NativeLayout.queryIndex]; omega⟩
  fin_cases call <;> fin_cases slot
  · carry_from_view source using hp,
      (NativeDiagonalView0.source0_lookup (p := p)), (NativeDiagonalView0.source0_eval w),
      NativeDiagonalView0.source0Values, NativeDiagonalView0.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView0.source2_lookup (p := p)), (NativeDiagonalView0.source2_eval w),
      NativeDiagonalView0.source2Values, NativeDiagonalView0.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView0.source10_lookup (p := p)), (NativeDiagonalView0.source10_eval w),
      NativeDiagonalView0.source10Values, NativeDiagonalView0.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView0.source11_lookup (p := p)), (NativeDiagonalView0.source11_eval w),
      NativeDiagonalView0.source11Values, NativeDiagonalView0.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView1.source0_lookup (p := p)), (NativeDiagonalView1.source0_eval w),
      NativeDiagonalView1.source0Values, NativeDiagonalView1.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView1.source2_lookup (p := p)), (NativeDiagonalView1.source2_eval w),
      NativeDiagonalView1.source2Values, NativeDiagonalView1.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView1.source10_lookup (p := p)), (NativeDiagonalView1.source10_eval w),
      NativeDiagonalView1.source10Values, NativeDiagonalView1.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView1.source11_lookup (p := p)), (NativeDiagonalView1.source11_eval w),
      NativeDiagonalView1.source11Values, NativeDiagonalView1.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView2.source0_lookup (p := p)), (NativeDiagonalView2.source0_eval w),
      NativeDiagonalView2.source0Values, NativeDiagonalView2.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView2.source2_lookup (p := p)), (NativeDiagonalView2.source2_eval w),
      NativeDiagonalView2.source2Values, NativeDiagonalView2.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView2.source10_lookup (p := p)), (NativeDiagonalView2.source10_eval w),
      NativeDiagonalView2.source10Values, NativeDiagonalView2.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView2.source11_lookup (p := p)), (NativeDiagonalView2.source11_eval w),
      NativeDiagonalView2.source11Values, NativeDiagonalView2.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView3.source0_lookup (p := p)), (NativeDiagonalView3.source0_eval w),
      NativeDiagonalView3.source0Values, NativeDiagonalView3.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView3.source2_lookup (p := p)), (NativeDiagonalView3.source2_eval w),
      NativeDiagonalView3.source2Values, NativeDiagonalView3.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView3.source10_lookup (p := p)), (NativeDiagonalView3.source10_eval w),
      NativeDiagonalView3.source10Values, NativeDiagonalView3.frame, 0
  · carry_from_view source using hp,
      (NativeDiagonalView3.source11_lookup (p := p)), (NativeDiagonalView3.source11_eval w),
      NativeDiagonalView3.source11Values, NativeDiagonalView3.frame, 0

/-- The first two C-addition carry flags remain native Boolean assertions. -/
theorem native_diagonal_first_c_flags {p : Nat} [Fact p.Prime]
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 2) :
    (diagonalFrame call w).cCarries[(slot.castLE (by decide) : Fin 4)] = 0 ∨
      (diagonalFrame call w).cCarries[(slot.castLE (by decide) : Fin 4)] = 1 := by
  have asserted := Verification.assertion_of_holds h
    ⟨NativeLayout.diagonalBooleanAssertion call slot, by
      rw [constraint_count]; have := call.isLt; have := slot.isLt
      dsimp [NativeLayout.diagonalBooleanAssertion]; omega⟩
  rw [NativeBooleanBindings.diagonal_expression (p := p)] at asserted
  rw [NativeBooleanBindings.diagonal_first_c_read (p := p) call slot w]
  simpa only [Verification.environment] using
    (Arithmetic.nativeBooleanExpression_eq_zero (p := p)
      (426 + 30 * call.val + 3 * slot.val) (Verification.environment w)).mp asserted

/-- The two final carry values are bounded by the native seven-bit carry table. -/
theorem native_diagonal_last_c_bounds {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) (slot : Fin 2) :
    (diagonalFrame call w).cCarries[(⟨2 + slot.val, by omega⟩ : Fin 4)].val < 3 := by
  have source := Verification.lookup_of_holds h
    ⟨NativeLayout.queryIndex .diagonal call NativeLayout.finalCarryQueries[slot], by
      rw [lookup_count]; have := call.isLt; have := NativeLayout.finalCarryQueries[slot].isLt
      dsimp [NativeLayout.queryIndex]; omega⟩
  fin_cases call <;> fin_cases slot
  · carry_from_view source using hp,
      (NativeDiagonalView0.source14_lookup (p := p)), (NativeDiagonalView0.source14_eval w),
      NativeDiagonalView0.source14Values, NativeDiagonalView0.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView0.source15_lookup (p := p)), (NativeDiagonalView0.source15_eval w),
      NativeDiagonalView0.source15Values, NativeDiagonalView0.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView1.source14_lookup (p := p)), (NativeDiagonalView1.source14_eval w),
      NativeDiagonalView1.source14Values, NativeDiagonalView1.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView1.source15_lookup (p := p)), (NativeDiagonalView1.source15_eval w),
      NativeDiagonalView1.source15Values, NativeDiagonalView1.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView2.source14_lookup (p := p)), (NativeDiagonalView2.source14_eval w),
      NativeDiagonalView2.source14Values, NativeDiagonalView2.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView2.source15_lookup (p := p)), (NativeDiagonalView2.source15_eval w),
      NativeDiagonalView2.source15Values, NativeDiagonalView2.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView3.source14_lookup (p := p)), (NativeDiagonalView3.source14_eval w),
      NativeDiagonalView3.source14Values, NativeDiagonalView3.frame, 1
  · carry_from_view source using hp,
      (NativeDiagonalView3.source15_lookup (p := p)), (NativeDiagonalView3.source15_eval w),
      NativeDiagonalView3.source15Values, NativeDiagonalView3.frame, 1

/-- Derive all flags from native acceptance and projected lookups. The shared
    G lemma derives the final two Boolean flags from bounded arithmetic. -/
theorem native_diagonal_flags_complete {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 262144)
    (compatible : SerializedInverse.Scale64 p) (call : Fin 4) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (queries : Blake2G.Proofs.QueryHolds (Blake2G.setupTable (fun _ => Vector.replicate 7 0))
      (diagonalFrame call w).assignment) :
    ∀ k : Fin 12,
      (diagonalFrame call w).base Blake2G.Variables.booleanColumns[1 + k.val] = 0 ∨
      (diagonalFrame call w).base Blake2G.Variables.booleanColumns[1 + k.val] = 1 :=
  (diagonalFrame call w).flags_from_queries hp compatible _ queries
    (native_diagonal_addition_carries (by omega) call h)
    (native_diagonal_first_c_flags call h)
    (native_diagonal_last_c_bounds (by omega) call h)

end Airbender.Blake2Round.Proofs
