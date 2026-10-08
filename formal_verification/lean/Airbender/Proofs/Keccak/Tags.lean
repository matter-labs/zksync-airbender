import Airbender.Proofs.Keccak.Controls
namespace Airbender.Keccak.Proofs
open Arithmetic
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
set_option warningAsError true

/-- Routing in `cs/src/gkr_circuits/delegation/keccak_special5/mod.rs`.
    IDs from `table_type.rs`: XOR=4, Iota-XOR=38, ANDN=39, rotation=40.
    This is routing bookkeeping, not another expression or lookup semantics. -/
def operationTags : Vector (Vector Nat 5) 7 := #v[
  #v[38, 4, 4, 4, 4], #v[40, 40, 4, 40, 4], #v[40, 4, 40, 4, 4],
  #v[4, 4, 4, 4, 4], #v[40, 40, 40, 40, 40],
  #v[39, 39, 4, 39, 4], #v[39, 4, 39, 4, 4]]

theorem operation_tags_bounded : ∀ j : Fin 7, ∀ k : Fin 5, operationTags[j][k] ≤ 40 := by decide

def byteTag {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (i : Fin 40) : ZMod p :=
  (((FlatOperation.lookups (importedConstraints setup)).get
    ⟨i.val + 2, by rw [lookup_count]; omega⟩).entry.toArray.back!).eval
      (Verification.environment w)

theorem tag_polynomial {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (i : Fin 40) :
    byteTag setup w i = ∑ mode : Fin 7,
      ((operationTags[mode][i.val / 8] : Nat) : ZMod p) * w Variables.modeColumns[mode] := by
  fin_cases i <;> simp [byteTag, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment, operationTags, Variables.modeColumns,
    Fin.sum_univ_succ]
  all_goals ring

theorem selected_tags {p : Nat} [Fact p.Prime] (hp : 41 ≤ p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 0 = 1) (mode : Fin 7) (selected : w Variables.modeColumns[mode] = 1) :
    ∀ i : Fin 40, (byteTag setup w i).val = operationTags[mode][i.val / 8] := by
  have count := (selector_counts (by omega) holds).1
  have one : (w 0).val = 1 := by rw [active]; simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
  have selectedValue : (w Variables.modeColumns[mode]).val = 1 := by
    rw [selected]; simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
  have unique (j : Fin 7) : w Variables.modeColumns[j] = if j = mode then 1 else 0 := by
    split_ifs with same
    · simpa only [same] using selected
    · have zero := sum_le_one_exclusive (by omega : (∑ i : Fin 7,
        (w Variables.modeColumns[i]).val) ≤ 1) mode selectedValue j same
      have cast := ZMod.natCast_zmod_val (w Variables.modeColumns[j])
      rw [zero] at cast
      simpa only [Nat.cast_zero] using cast.symm
  intro i
  rw [tag_polynomial]
  simp_rw [unique]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply ZMod.val_natCast_of_lt
  have group : i.val / 8 < 5 := by omega
  have bound : operationTags[mode][i.val / 8] ≤ 40 := by
    exact operation_tags_bounded mode ⟨i.val / 8, group⟩
  omega

/-- Inactive rows route every byte query to the setup's zero entry. Contents
    and padding are still enforced only by the supplied lookup relation. -/
theorem inactive_tags {p : Nat} [Fact p.Prime] (hp : 7 < p)
    {setup : Table (ZMod p) (fields 8)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (inactive : w 0 = 0) : ∀ i : Fin 40, byteTag setup w i = 0 := by
  have count := (selector_counts hp holds).1
  rw [inactive, ZMod.val_zero] at count
  have zeros (j : Fin 7) : w Variables.modeColumns[j] = 0 := by
    have below : (w Variables.modeColumns[j]).val ≤ ∑ i : Fin 7, (w Variables.modeColumns[i]).val :=
      Finset.single_le_sum (f := fun i : Fin 7 => (w Variables.modeColumns[i]).val)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [count] at below
    have cast := ZMod.natCast_zmod_val (w Variables.modeColumns[j])
    rw [Nat.eq_zero_of_le_zero below] at cast
    simpa only [Nat.cast_zero] using cast.symm
  intro i
  rw [tag_polynomial]
  simp only [zeros, mul_zero, Finset.sum_const_zero]

end Airbender.Keccak.Proofs
