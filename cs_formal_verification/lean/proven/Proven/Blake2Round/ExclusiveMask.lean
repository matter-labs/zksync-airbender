module
public import Proven.Blake2Round.Control
public import Human.Circuits.Blake2Round.Memory
public import Proven.CleanCore.Circuit.Operations
public import Proven.Defs.Circuits.Blake2Round.Artifact

@[expose] public section

namespace Airbender.Blake2Round.Proofs
open Arithmetic
set_option warningAsError true

private def packedBits {p : Nat} (w : Nat → ZMod p) : Nat := (w 139).val + 2 * (w 140).val + 4 * (w 141).val +
    8 * (w 142).val + 16 * (w 143).val + 32 * (w 144).val +
    64 * (w 145).val + 128 * (w 146).val + 256 * (w 147).val +
    512 * (w 148).val + 1024 * (w 149).val + 2048 * (w 150).val + 4096 * (w 151).val

private theorem control_columns : ∀ i : Fin 13, Variables.controlBits[i] = 139 + i.val := by
  decide

private theorem round_columns : ∀ i : Fin 10, Variables.roundBits[i] = 142 + i.val := by decide

/-- The thirteen control bits are Boolean. -/
private theorem control_bit {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 6)}
    {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (k : Nat) (hk : k < 13) : (w (139 + k)).val ≤ 1 :=
  control_columns ⟨k, hk⟩ ▸ boolean_val (Control.Proofs.control_bits holds ⟨k, hk⟩)

private theorem control_encoding [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    packedBits w = (w Variables.controlReadHi).val := by
  have b0 := control_bit holds 0 (by decide); have b1 := control_bit holds 1 (by decide)
  have b2 := control_bit holds 2 (by decide); have b3 := control_bit holds 3 (by decide)
  have b4 := control_bit holds 4 (by decide); have b5 := control_bit holds 5 (by decide)
  have b6 := control_bit holds 6 (by decide); have b7 := control_bit holds 7 (by decide)
  have b8 := control_bit holds 8 (by decide); have b9 := control_bit holds 9 (by decide)
  have b10 := control_bit holds 10 (by decide); have b11 := control_bit holds 11 (by decide)
  have b12 := control_bit holds 12 (by decide)
  simp only [Nat.reduceAdd] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
  have equation := Verification.assertion_of_holds holds ⟨1, by rw [constraint_count]; decide⟩
  op_index at equation
  simp only [Expression.eval, Verification.environment] at equation
  push_cast at equation
  have field : (packedBits w : ZMod p) = w Variables.controlReadHi := by
    simp only [packedBits, Variables.controlReadHi, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination equation
  have bound : packedBits w < p := by dsimp [packedBits]; omega
  rw [← field, ZMod.val_natCast_of_lt bound]

/-- A sum of weighted bits that is a power of two has exactly that bit set. -/
theorem one_hot_bits : ∀ (n : Nat) (b : Nat → Nat) (r : Nat), (∀ k < n, b k ≤ 1) →
    (∑ k ∈ Finset.range n, 2 ^ k * b k) = 2 ^ r → r < n →
    ∀ k < n, b k = if k = r then 1 else 0
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, b, r, hb, sum, hr => by
    have split : ∑ k ∈ Finset.range (n + 1), 2 ^ k * b k =
        b 0 + 2 * ∑ i ∈ Finset.range n, 2 ^ i * b (i + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [split] at sum
    have b0 := hb 0 (by omega)
    intro k hk
    cases r with
    | zero =>
      rw [pow_zero] at sum
      have low : b 0 = 1 := by omega
      have rest : ∑ i ∈ Finset.range n, 2 ^ i * b (i + 1) = 0 := by omega
      cases k with
      | zero => simp [low]
      | succ k =>
        have term := (Finset.sum_eq_zero_iff.mp rest) k (Finset.mem_range.mpr (by omega))
        simp only [mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and,
          false_or] at term
        simp [term]
    | succ r =>
      rw [pow_succ] at sum
      have low : b 0 = 0 := by omega
      have rest : ∑ i ∈ Finset.range n, 2 ^ i * b (i + 1) = 2 ^ r := by omega
      have shifted := one_hot_bits n (fun i => b (i + 1)) r (fun i hi => hb (i + 1) (by omega)) rest
        (by omega)
      cases k with
      | zero => simp [low]
      | succ k => simpa using shifted k (by omega)

theorem exclusive_mask [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (flags : Fin 8) (round : Fin 10)
    (read : (w Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val) :
    Memory.RoundMask w round := by
  have bits := control_bit holds
  have natural := (control_encoding hp holds).trans read
  dsimp [packedBits] at natural
  have high : ∑ k ∈ Finset.range 10, 2 ^ k * (w (142 + k)).val = 2 ^ round.val := by
    have b0 := bits 0 (by decide); have b1 := bits 1 (by decide); have b2 := bits 2 (by decide)
    have b3 := bits 3 (by decide); have b4 := bits 4 (by decide); have b5 := bits 5 (by decide)
    have b6 := bits 6 (by decide); have b7 := bits 7 (by decide); have b8 := bits 8 (by decide)
    have b9 := bits 9 (by decide); have b10 := bits 10 (by decide)
    have b11 := bits 11 (by decide); have b12 := bits 12 (by decide)
    simp only [Nat.reduceAdd] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reducePow,
      zero_add, one_mul]
    have flagsBound := flags.isLt
    omega
  have hot := one_hot_bits 10 (fun k => (w (142 + k)).val) round.val
    (fun k hk => by rw [show 142 + k = 139 + (3 + k) by omega]; exact bits (3 + k) (by omega))
    high round.isLt
  have prime := (Fact.out : p.Prime).one_lt
  let : Fact (1 < p) := ⟨prime⟩
  intro i
  rw [round_columns i]
  apply ZMod.val_injective
  have bit := hot i.val i.isLt
  by_cases e : i = round
  · simp only [e, ↓reduceIte] at bit ⊢
    rw [bit, ZMod.val_one]
  · simp only [Fin.val_eq_val, e, ↓reduceIte] at bit ⊢
    rw [bit, ZMod.val_zero]

theorem control_flags [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 6)} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (flags : Fin 8) (round : Fin 10)
    (read : (w Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val) :
    (w 139).val = flags.val % 2 ∧ (w 140).val = flags.val / 2 % 2 ∧
      (w 141).val = flags.val / 4 := by
  have b0 := boolean_val (Control.Proofs.control_bits holds 0)
  have b1 := boolean_val (Control.Proofs.control_bits holds 1)
  have b2 := boolean_val (Control.Proofs.control_bits holds 2)
  change (w 139).val ≤ 1 at b0
  change (w 140).val ≤ 1 at b1
  change (w 141).val ≤ 1 at b2
  have natural := (control_encoding hp holds).trans read
  dsimp [packedBits] at natural
  have flagsBound := flags.isLt
  have low : (w 139).val + 2 * (w 140).val + 4 * (w 141).val = flags.val := by omega
  omega

end Airbender.Blake2Round.Proofs
