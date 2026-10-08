import Airbender.Review.Trace.Columns
import Airbender.Proofs.Arithmetic.Lemmas

namespace Airbender.Trace.Proofs

theorem range_bound {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Environment (ZMod p)} (h : (timestampLookup entry).Contains env) :
    (entry.eval env).val < timestampBase := by
  have hs := (timestampLookup entry).table.imply_soundness _ _ h
  exact (Lookup.soundess_def_field timestampTable env entry).mp hs

theorem range_contains {p : Nat} [Fact p.Prime] {entry : Expression (ZMod p)}
    {env : Environment (ZMod p)} (h : (entry.eval env).val < timestampBase) :
    (timestampLookup entry).Contains env := by
  have hc := (Lookup.completeness_def_field timestampTable env entry).mpr h
  exact (timestampLookup entry).table.implied_by_completeness _ _ hc

/-- Lift the two limb equations separately: the full 38-bit clock need not fit
    in the outer field. Final-limb bounds prevent high-limb overflow. -/
theorem increment {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {initial final : Timestamp} (initialBound : initial.Bounded) (finalBound : final.Bounded)
    {carry : Nat} (bit : carry ≤ 1)
    (low : (initial.lo : ZMod p) + 4 = final.lo + timestampBase * carry)
    (high : (initial.hi : ZMod p) + carry = final.hi) :
    final.value = initial.value + 4 := by
  rcases initialBound with ⟨il, ih⟩
  rcases finalBound with ⟨fl, fh⟩
  simp only [timestampBase] at *
  have lowNat : initial.lo + 4 = final.lo + 524288 * carry :=
    Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by nlinarith) (by exact_mod_cast low)
  have highNat : initial.hi + carry = final.hi :=
    Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by omega) (by exact_mod_cast high)
  simp only [Timestamp.value, timestampBase]
  omega

/-- Exactly the two expressions emitted by Rust's
    `compile_timestamp_comparison_range_checks`. Bounds turn the borrowed
    subtraction into strict previous-write order. -/
theorem comparison {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {initial previous : Timestamp} (initialBound : initial.Bounded)
    (previousBound : previous.Bounded) {offset carry : Nat} (offsetBound : offset < 4)
    (aligned : initial.lo % 4 = 0) (bit : carry ≤ 1)
    (low : ((previous.lo : ZMod p) - initial.lo - offset + timestampBase * carry).val < timestampBase)
    (high : ((previous.hi : ZMod p) + timestampBase - carry - initial.hi).val < timestampBase) :
    previous.value < initial.value + offset := by
  rcases initialBound with ⟨il, ih⟩
  rcases previousBound with ⟨pl, ph⟩
  simp only [timestampBase] at *
  have currentLow : initial.lo + offset < timestampBase := by
    change initial.lo + offset < 524288
    have remainder := Nat.mod_add_div initial.lo 4
    omega
  let lowResult : ZMod p := previous.lo - initial.lo - offset + timestampBase * carry
  let highResult : ZMod p := previous.hi + timestampBase - carry - initial.hi
  have lowBound : lowResult.val < 524288 := low
  have highBound : highResult.val < 524288 := high
  have lowEq : (lowResult.val : ZMod p) + (initial.lo + offset : Nat) =
      (previous.lo + timestampBase * carry : Nat) := by
    dsimp [lowResult]
    simp only [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul]
    ring
  have highEq : (highResult.val + carry + initial.hi : Nat) =
      (previous.hi + 524288 : Nat) := by
    apply Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by omega)
    simp only [Nat.cast_add, ZMod.natCast_zmod_val]
    dsimp [highResult]
    ring
  have lowNat : lowResult.val + (initial.lo + offset) = previous.lo + 524288 * carry :=
    Arithmetic.bounded_nat_eq (F := ZMod p) (p := p)
      (by simp only [timestampBase] at currentLow; omega)
      (by omega) (by exact_mod_cast lowEq)
  simp only [Timestamp.value, timestampBase]
  rcases (show carry = 0 ∨ carry = 1 by omega) with rfl | rfl
  · have strict : previous.hi < initial.hi := by omega
    omega
  · simp only [Nat.mul_one] at lowNat
    have le : previous.hi ≤ initial.hi := by omega
    by_cases equal : previous.hi = initial.hi
    · rw [equal]
      omega
    · have strict : previous.hi < initial.hi := by omega
      omega

theorem distinct_slots {initial : Timestamp} {left right : Nat} (different : left ≠ right) :
    initial.value + left ≠ initial.value + right := by omega

end Airbender.Trace.Proofs
