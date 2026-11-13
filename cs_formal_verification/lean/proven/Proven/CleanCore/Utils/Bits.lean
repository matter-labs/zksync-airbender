module
public import Proven.CleanCore.Utils.Fin
public import Proven.CleanCore.Utils.Vector
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
-- Clean's Mathlib/Lean imports for this file, re-exported so importers see what they saw through Clean
public import Lean.Meta.Tactic.Simp.RegisterCommand
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Basic

/-! # Bit decomposition of naturals and field elements (Clean `Clean.Utils.Bits`, pinned b41c196): transcribed with proofs.
`F p` is `ZMod p`. -/

@[expose] public section

namespace Airbender

namespace Utils.Bits
/--
  Convert a natural number to a vector of bits.
-/
def toBits (n : ℕ) (x : ℕ) : Vector ℕ n :=
  Vector.mapRange n fun i => if x.testBit i then 1 else 0

/--
  Convert a vector of bits to a natural number.
-/
def fromBits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

/--
  Main lemma which establishes the behaviour of `fromBits`
  and `toBits` by induction
-/
theorem toBits_fromBits_aux {n : ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fromBits bits) < 2^n ∧ toBits n (fromBits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [fromBits, toBits, Vector.getElem_mapRange]
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    let bits' : Vector ℕ n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j] = 0 ∨ bits'[j] = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    have h_bits_n : bits[n] = 0 ∨ bits[n] = 1 := h_bits n (Nat.lt_succ_self _)
    obtain ⟨ ih_lt, ih_eq ⟩ := ih bits' h_bits'

    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    let xn : ℕ := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2 ^ i)) 0
    have : bits[n] ≤ 1 := by rcases h_bits_n <;> simp only [zero_le, le_refl, *]
    have h_lt : xn + bits[n] * 2^n < 2^(n+1) := by
      have : bits[n] * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
      rw [Nat.pow_succ']
      linarith

    constructor
    · exact h_lt
    · intro i hi
      rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
      by_cases hin : i < n <;> simp only [hin, reduceIte]
      · exact ih_eq i hin
      · have : n = i := by linarith
        subst this
        rcases h_bits_n <;> simp [*]

variable {p : ℕ} [prime: Fact p.Prime]
/--
Convert a field element to a vector of bits, which are themselves field elements.
-/
def fieldToBits (n : ℕ) (x : ZMod p) : Vector (ZMod p) n :=
  .map (↑) (toBits n x.val)

/--
Convert a vector of bits to a field element.
-/
def fieldFromBits {n : ℕ} (bits : Vector (ZMod p) n) : ZMod p :=
  fromBits <| bits.map ZMod.val

/--
Define the behaviour of `fieldFromBits` and `fieldToBits` by
lifting `toBits_fromBits_aux`
-/
theorem fieldToBits_fieldFromBits_aux {n : ℕ} (hn : 2^n < p) (bits : Vector (ZMod p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fieldFromBits bits).val < 2^n ∧ fieldToBits n (fieldFromBits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [fieldFromBits, fieldToBits]

  have h_bool : ∀ i (hi : i < n), (bits.map ZMod.val)[i] = 0 ∨ (bits.map ZMod.val)[i] = 1 := by
    intro i hi
    specialize h_bits i hi
    apply Or.elim h_bits
    · intro h; apply Or.inl; simp only [Vector.getElem_map, ZMod.val_eq_zero]; assumption
    · intro h; apply Or.inr; simp only [Vector.getElem_map]
      apply_fun ZMod.val at h
      simp only [ZMod.val_one] at h
      exact h

  obtain ⟨thm_lt, thm_val⟩ := toBits_fromBits_aux (bits.map ZMod.val) h_bool
  constructor
  · rw [ZMod.val_natCast_of_lt (by linarith)]
    exact thm_lt
  · intro i hi
    simp
    have h_lt : fromBits (Vector.map ZMod.val bits) < p := by linarith
    simp_rw [Nat.mod_eq_of_lt h_lt, thm_val]
    simp

/-- `fieldToBits` is a left-inverse of `fieldFromBits` -/
theorem fieldToBits_fieldFromBits {n : ℕ} (hn : 2^n < p) (bits : Vector (ZMod p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    fieldToBits n (fieldFromBits bits) = bits := (fieldToBits_fieldFromBits_aux hn bits h_bits).right

end Utils.Bits

end Airbender
