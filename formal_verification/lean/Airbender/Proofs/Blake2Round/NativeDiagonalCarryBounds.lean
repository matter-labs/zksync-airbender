import Airbender.Proofs.Blake2Round.NativeCarryBounds
import Airbender.Proofs.Blake2Round.NativeDiagonalView0
import Airbender.Proofs.Blake2Round.NativeDiagonalView1
import Airbender.Proofs.Blake2Round.NativeDiagonalView2
import Airbender.Proofs.Blake2Round.NativeDiagonalView3

namespace Airbender.Blake2Round.Proofs.NativeDiagonalCarryBounds
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

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

theorem addition_bound {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) (slot : Fin 4) {w : Nat → ZMod p}
    (source : ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal call NativeLayout.additionCarryQueries[slot], by
        rw [lookup_count]; have := call.isLt; have := NativeLayout.additionCarryQueries[slot].isLt
        dsimp [NativeLayout.queryIndex]; omega⟩).Contains (Verification.environment w)) :
    (diagonalFrame call w).addCarries[slot].val < 3 := by
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

theorem final_c_bound {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) (slot : Fin 2) {w : Nat → ZMod p}
    (source : ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .diagonal call NativeLayout.finalCarryQueries[slot], by
        rw [lookup_count]; have := call.isLt; have := NativeLayout.finalCarryQueries[slot].isLt
        dsimp [NativeLayout.queryIndex]; omega⟩).Contains (Verification.environment w)) :
    (diagonalFrame call w).cCarries[(⟨2 + slot.val, by omega⟩ : Fin 4)].val < 3 := by
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

end Airbender.Blake2Round.Proofs.NativeDiagonalCarryBounds
