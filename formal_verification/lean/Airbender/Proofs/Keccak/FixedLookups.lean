import Airbender.Proofs.Keccak.FixedTables
import Airbender.Proofs.Keccak.Lookups

namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private theorem byte_tag_not_controller {p : Nat} [Fact p.Prime] (hp : 41 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 40) : (byteTag setup w i).val ≠ 37 := by
  rcases (control_bits h).1 with inactive | active
  · rw [inactive_tags (by omega) h inactive]
    norm_num
  · have count := (selector_counts (by omega) h).1
    rw [active] at count
    have one : (1 : ZMod p).val = 1 := by
      simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
    rw [one] at count
    have positive : 0 < ∑ j : Fin 7, (w Variables.modeColumns[j]).val := by omega
    obtain ⟨mode, _, modePositive⟩ := Finset.sum_pos_iff.mp positive
    have flag := (control_bits h).2 ⟨mode.val, by omega⟩
    have below : (w Variables.modeColumns[mode]).val ≤ 1 := by
      fin_cases mode <;> exact boolean_val flag
    have value : (w Variables.modeColumns[mode]).val = 1 := by omega
    have cast := ZMod.natCast_zmod_val (w Variables.modeColumns[mode])
    rw [value] at cast
    have selected : w Variables.modeColumns[mode] = 1 := by
      simpa only [Nat.cast_one] using cast.symm
    rw [selected_tags hp h active mode selected i]
    have tags : ∀ m : Fin 7, ∀ group : Fin 5, operationTags[m][group] ≠ 37 := by
      intro m group
      fin_cases m <;> fin_cases group <;> norm_num [operationTags]
    exact tags mode ⟨i.val / 8, by omega⟩

/-- Every byte query, in every active mode and in padding, is interpreted by
    Clean's native membership. Controller rows cannot masquerade as byte rows. -/
theorem byte_lookup_checks {p : Nat} [Fact p.Prime] (hp : 1048576 ≤ p)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) : ByteLookupChecks control w := by
  intro i
  have distinct := byte_tag_not_controller (by omega) h i
  have member := Verification.lookup_of_holds h
    ⟨i.val + 2, by rw [lookup_count]; omega⟩
  change (byteQuery (setupTable control) i).Contains (Verification.environment w) at member
  let entry := byteEntry (setupTable (p := p) control) i
  have shape : byteQuery (setupTable control) i = Lookup.mk (setupTable control).toRaw entry :=
    byte_query_shape (setupTable control) i
  have column (j : Nat) (hj : j < 8) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by simpa only [Vector.size_toArray] using hj)]
    rfl
  unfold byteTag at distinct
  rw [shape] at distinct member
  simp only [Array.back!, Vector.size_toArray] at distinct
  change (entry.toArray[7]!.eval (Verification.environment w)).val ≠ 37 at distinct
  rw [column 7 (by decide)] at distinct
  have relation := fixed_lookup hp member distinct
  change let raw := (byteQuery (setupTable control) i).entry.toArray
    ByteOperationFacts (raw[7]!.eval (Verification.environment w)).val
      (raw[0]!.eval (Verification.environment w)).val
      (raw[1]!.eval (Verification.environment w)).val
      (raw[2]!.eval (Verification.environment w)).val
  rw [shape]
  simpa only [Lookup.entry, column 7 (by decide), column 0 (by decide),
    column 1 (by decide), column 2 (by decide)] using relation

end Airbender.Keccak.Proofs
