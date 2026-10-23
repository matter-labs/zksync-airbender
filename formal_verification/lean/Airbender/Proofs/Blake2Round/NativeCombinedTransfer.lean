import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2Round.NativeXorTransfer

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem combined_payload {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {source : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (selected : source[5].eval env = 57) :
    ∃ n, n < 16384 ∧ source.map (Expression.eval env) =
      (combinedXorRow n).map (fun value : Nat => (value : ZMod p)) := by
  have tag : nativeTags[(5 : Fin 6)] = 57 := rfl
  obtain ⟨n, bound, row⟩ := selected_region hp 5 member (by rw [tag]; exact selected)
  have reference : referenceRegionRow 5 n = combinedXorRow n := rfl
  rw [reference] at row
  change n < 16384 at bound
  exact ⟨n, bound, row⟩

/-- The imported packed XOR output splits into its two actual bounded XORs. -/
theorem combined_output_slices {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (n : Nat) (bound : n < 16384) :
    let low := n / 1024 ^^^ n / 8 % 16;
    let high := n / 128 % 8 ^^^ n % 8;
    combinedLow (((low + 16 * high : Nat) : ZMod p)) = ((low : Nat) : ZMod p) ∧
      combinedHigh (((low + 16 * high : Nat) : ZMod p)) = ((high : Nat) : ZMod p) := by
  let low := n / 1024 ^^^ n / 8 % 16
  let high := n / 128 % 8 ^^^ n % 8
  have lo : low < 2 ^ 4 := Nat.xor_lt_two_pow (by omega) (by omega)
  have hi : high < 2 ^ 3 := Nat.xor_lt_two_pow (by omega) (by omega)
  norm_num only [Nat.reducePow] at lo hi
  have native : (((low + 16 * high : Nat) : ZMod p)).val = low + 16 * high :=
    ZMod.val_natCast_of_lt (by omega)
  have lower : (low + 16 * high) % 16 = low := by omega
  have upper : (low + 16 * high) / 16 = high := by omega
  constructor
  · change (((((low + 16 * high : Nat) : ZMod p)).val % 16 : Nat) : ZMod p) = (low : ZMod p)
    rw [native, lower]
  · change (((((low + 16 * high : Nat) : ZMod p)).val / 16 : Nat) : ZMod p) = (high : ZMod p)
    rw [native, upper]

theorem combined_low_membership {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (control : Fin 512 → Vector Nat 7)
    {source : Vector (Expression (ZMod p)) 6} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)}
    (member : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (selected : source[5].eval sourceEnv = 57)
    (columns : target.map (Expression.eval targetEnv) = combinedLowPad (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable control).toRaw target).Contains targetEnv := by
  obtain ⟨n, bound, row⟩ := combined_payload hp member selected
  have output := (combined_output_slices hp n bound).1
  apply g_xor_membership control 2 (n / 1024) (n / 8 % 16)
  · change _ < 16
    omega
  · change _ < 16
    omega
  · rw [columns, row]
    apply Vector.ext
    intro j hj
    interval_cases j
    all_goals simp only [combinedLowPad, combinedXorRow, gTags, Fin.getElem_fin,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals first | exact output | simp

theorem combined_high_membership {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    (control : Fin 512 → Vector Nat 7)
    {source : Vector (Expression (ZMod p)) 6} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)}
    (member : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (selected : source[5].eval sourceEnv = 57)
    (columns : target.map (Expression.eval targetEnv) = combinedHighPad (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable control).toRaw target).Contains targetEnv := by
  obtain ⟨n, bound, row⟩ := combined_payload hp member selected
  have output := (combined_output_slices hp n bound).2
  apply g_xor_membership control 1 (n / 128 % 8) (n % 8)
  · change _ < 8
    omega
  · change _ < 8
    omega
  · rw [columns, row]
    apply Vector.ext
    intro j hj
    interval_cases j
    all_goals simp only [combinedHighPad, combinedXorRow, gTags, Fin.getElem_fin,
      Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    all_goals first | exact output | simp

end Airbender.Blake2Round.Proofs
