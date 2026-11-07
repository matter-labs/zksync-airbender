import Airbender.Proofs.Blake2Round.NativeCarryBounds
import Airbender.Proofs.Blake2Round.NativeColumnSources0
import Airbender.Proofs.Blake2Round.NativeColumnSources1
import Airbender.Proofs.Blake2Round.NativeColumnSources2
import Airbender.Proofs.Blake2Round.NativeColumnSources3

namespace Airbender.Blake2Round.Proofs.NativeColumnCarryBounds
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

local macro "column_carry_from_view " member:ident " using " hp:term ", " binding:term ", " evaluated:term ", " values:ident : tactic =>
  `(tactic| (
    have membership := $member
    simp only [NativeLayout.additionCarryQueries, Vector.getElem_mk, Fin.getElem_fin,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at membership
    have normalizedBinding := $binding
    norm_num [NativeLayout.queryIndex] at normalizedBinding membership
    rw [normalizedBinding] at membership
    have bound := carry_values_bound $hp (0 : Fin 2) membership $evaluated (by
      unfold $values:ident
      norm_num [carryTags])
    unfold $values:ident at bound
    simpa [NativeLayout.columnCarryColumns] using bound))

/-- A checked native carry query bounds its selected witness value. -/
theorem query_bound {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (call : Fin 4) (slot : Fin 4) {w : Nat → ZMod p}
    (source : ((FlatOperation.lookups (importedConstraints setupTable)).get
      ⟨NativeLayout.queryIndex .column call NativeLayout.additionCarryQueries[slot], by
        rw [lookup_count]; have := call.isLt; have := NativeLayout.additionCarryQueries[slot].isLt
        dsimp [NativeLayout.queryIndex]; omega⟩).Contains (Verification.environment w)) :
    (w ((NativeLayout.columnCarryColumns call)[slot])).val < 3 := by
  fin_cases call <;> fin_cases slot
  · column_carry_from_view source using hp,
      (NativeColumnView0.source0_lookup (p := p)), (NativeColumnView0.source0_eval w), NativeColumnView0.source0Values
  · column_carry_from_view source using hp,
      (NativeColumnView0.source2_lookup (p := p)), (NativeColumnView0.source2_eval w), NativeColumnView0.source2Values
  · column_carry_from_view source using hp,
      (NativeColumnView0.source10_lookup (p := p)), (NativeColumnView0.source10_eval w), NativeColumnView0.source10Values
  · column_carry_from_view source using hp,
      (NativeColumnView0.source11_lookup (p := p)), (NativeColumnView0.source11_eval w), NativeColumnView0.source11Values
  · column_carry_from_view source using hp,
      (NativeColumnView1.source0_lookup (p := p)), (NativeColumnView1.source0_eval w), NativeColumnView1.source0Values
  · column_carry_from_view source using hp,
      (NativeColumnView1.source2_lookup (p := p)), (NativeColumnView1.source2_eval w), NativeColumnView1.source2Values
  · column_carry_from_view source using hp,
      (NativeColumnView1.source10_lookup (p := p)), (NativeColumnView1.source10_eval w), NativeColumnView1.source10Values
  · column_carry_from_view source using hp,
      (NativeColumnView1.source11_lookup (p := p)), (NativeColumnView1.source11_eval w), NativeColumnView1.source11Values
  · column_carry_from_view source using hp,
      (NativeColumnView2.source0_lookup (p := p)), (NativeColumnView2.source0_eval w), NativeColumnView2.source0Values
  · column_carry_from_view source using hp,
      (NativeColumnView2.source2_lookup (p := p)), (NativeColumnView2.source2_eval w), NativeColumnView2.source2Values
  · column_carry_from_view source using hp,
      (NativeColumnView2.source10_lookup (p := p)), (NativeColumnView2.source10_eval w), NativeColumnView2.source10Values
  · column_carry_from_view source using hp,
      (NativeColumnView2.source11_lookup (p := p)), (NativeColumnView2.source11_eval w), NativeColumnView2.source11Values
  · column_carry_from_view source using hp,
      (NativeColumnView3.source0_lookup (p := p)), (NativeColumnView3.source0_eval w), NativeColumnView3.source0Values
  · column_carry_from_view source using hp,
      (NativeColumnView3.source2_lookup (p := p)), (NativeColumnView3.source2_eval w), NativeColumnView3.source2Values
  · column_carry_from_view source using hp,
      (NativeColumnView3.source10_lookup (p := p)), (NativeColumnView3.source10_eval w), NativeColumnView3.source10Values
  · column_carry_from_view source using hp,
      (NativeColumnView3.source11_lookup (p := p)), (NativeColumnView3.source11_eval w), NativeColumnView3.source11Values

end Airbender.Blake2Round.Proofs.NativeColumnCarryBounds
