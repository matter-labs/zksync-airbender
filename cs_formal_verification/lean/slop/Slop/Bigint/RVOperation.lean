module
public import Slop.Bigint.NativeExecution
public import Slop.Bigint.Memory
public import Slop.Bigint.Control
public import Slop.Bigint.RVSpec

@[expose] public section

/-! One bigint row is the spec's `bigintOp` (`RV.Delegation.bigint`) on its port values: the x12 control byte selects
    the same operation, and the written limbs and returned x12 are the operation's result `mod 2²⁵⁶` and flag. The
    no-opcode row is covered: the circuit writes zero limbs and x12 = 0 (`empty_writes`), the spec's `(0, false)`.
    State-free. -/

namespace Airbender.Bigint.Proofs
open Arithmetic Native
set_option warningAsError true
set_option maxRecDepth 16384

private theorem carry_split {s V l : Nat} (bound : V < 2 ^ 256) (bit : l ≤ 1) (sum : s = V + 2 ^ 256 * l) :
    V = s % 2 ^ 256 ∧ l = if 2 ^ 256 ≤ s then 1 else 0 := by
  constructor
  · omega
  · split <;> omega

private theorem borrow_split {a b V l : Nat} (bound : V < 2 ^ 256) (bit : l ≤ 1) (sum : V + b = a + 2 ^ 256 * l) :
    V = (2 ^ 256 + a - b) % 2 ^ 256 ∧ l = if a < b then 1 else 0 := by
  constructor
  · omega
  · split <;> omega

/-- Equal values of canonical limb vectors are equal limbs. -/
theorem value_injective {l l' : Vector Nat 16} (bounded : ∀ i : Fin 16, l[i] < 65536)
    (bounded' : ∀ i : Fin 16, l'[i] < 65536) (same : value l = value l') : l = l' := by
  have words (i : Fin 8) : l[2 * i.val] + 65536 * l[2 * i.val + 1] = l'[2 * i.val] + 65536 * l'[2 * i.val + 1] := by
    have left := ofU256_of_limbs (value l) l bounded (Nat.mod_eq_of_lt (value_lt bounded)).symm i
    have right := ofU256_of_limbs (value l) l' bounded' (by rw [same]; exact (Nat.mod_eq_of_lt (value_lt bounded')).symm) i
    have lo := bounded ⟨2 * i.val, by omega⟩
    have hi := bounded ⟨2 * i.val + 1, by omega⟩
    have lo' := bounded' ⟨2 * i.val, by omega⟩
    have hi' := bounded' ⟨2 * i.val + 1, by omega⟩
    simp only [Fin.getElem_fin] at lo hi lo' hi'
    have bits := congrArg BitVec.toNat (left.symm.trans right)
    simp only [BitVec.toNat_ofNat] at bits
    omega
  apply Vector.ext
  intro j hj
  have pair := words ⟨j / 2, by omega⟩
  have lo := bounded ⟨2 * (j / 2), by omega⟩
  have hi := bounded ⟨2 * (j / 2) + 1, by omega⟩
  have lo' := bounded' ⟨2 * (j / 2), by omega⟩
  have hi' := bounded' ⟨2 * (j / 2) + 1, by omega⟩
  simp only [Fin.getElem_fin] at lo hi lo' hi'
  rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have index : 2 * ((k + k) / 2) = k + k := by omega
    simp only [index] at pair lo hi lo' hi'
    omega
  · have index' : 2 * ((2 * k + 1) / 2) = 2 * k := by omega
    simp only [index'] at pair lo hi lo' hi'
    omega

private theorem bool_val {x : ZMod babyBearModulus} (bit : x = 0 ∨ x = 1) : (x.val == 1).toNat = x.val := by
  rcases bit with zero | one
  · simp [zero]
  · simp [one, ZMod.val_one'' (by decide : babyBearModulus ≠ 1)]

theorem bit_val {x : ZMod babyBearModulus} (bit : x = 0 ∨ x = 1) : x.val = 0 ∨ x.val = 1 := by
  rcases bit with zero | one
  · simp [zero]
  · simp [one, ZMod.val_one'' (by decide : babyBearModulus ≠ 1)]

/-- x12's low limb is the control byte of the eight control columns (`Control.spec`). -/
theorem mask_columns {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    (w 55).val = (w 59).val + 2 * (w 60).val + 4 * (w 61).val + 8 * (w 62).val + 16 * (w 63).val +
      32 * (w 64).val + 64 * (w 65).val + 128 * (w 66).val ∧ (w 55).val < 256 := by
  have spec := Control.Proofs.soundness (by decide) setupTable ⟨(w 55).val, (w 56).val⟩
    ⟨⟨(w 57).val, (w 58).val⟩, Vector.ofFn fun i => (w Variables.controlBits[i]).val == 1⟩ w
    ⟨holds, rfl, rfl, rfl⟩
  have mask : (w 55).val = Control.mask (Vector.ofFn fun i => (w Variables.controlBits[i]).val == 1) := spec.1
  have b0 : w 59 = 0 ∨ w 59 = 1 := Control.Proofs.control_bits holds 0
  have b1 : w 60 = 0 ∨ w 60 = 1 := Control.Proofs.control_bits holds 1
  have b2 : w 61 = 0 ∨ w 61 = 1 := Control.Proofs.control_bits holds 2
  have b3 : w 62 = 0 ∨ w 62 = 1 := Control.Proofs.control_bits holds 3
  have b4 : w 63 = 0 ∨ w 63 = 1 := Control.Proofs.control_bits holds 4
  have b5 : w 64 = 0 ∨ w 64 = 1 := Control.Proofs.control_bits holds 5
  have b6 : w 65 = 0 ∨ w 65 = 1 := Control.Proofs.control_bits holds 6
  have b7 : w 66 = 0 ∨ w 66 = 1 := Control.Proofs.control_bits holds 7
  simp only [Control.mask, Fin.sum_univ_succ, Fin.sum_univ_zero] at mask
  simp only [Variables.controlBits, Fin.val_zero, Fin.val_succ, Fin.getElem_fin] at mask
  norm_num at mask
  rw [bool_val b0, bool_val b1, bool_val b2, bool_val b3, bool_val b4, bool_val b5, bool_val b6,
    bool_val b7] at mask
  exact ⟨by omega, spec.2.1⟩

/-- The control byte: one operation bit (or none) plus the carry bit 6. -/
theorem control_cases {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    ((∀ i : Fin 7, w Variables.operations[i] = 0) ∧ (w 55).val = 64 * (w 65).val) ∨
      ∃ chosen : Fin 7, w Variables.operations[chosen] = 1 ∧
        (w 55).val = 2 ^ (#v[0, 1, 2, 3, 4, 5, 7] : Vector Nat 7)[chosen] + 64 * (w 65).val := by
  have columns := (mask_columns holds).1
  have b0 : w 59 = 0 ∨ w 59 = 1 := Control.Proofs.control_bits holds 0
  have b1 : w 60 = 0 ∨ w 60 = 1 := Control.Proofs.control_bits holds 1
  have b2 : w 61 = 0 ∨ w 61 = 1 := Control.Proofs.control_bits holds 2
  have b3 : w 62 = 0 ∨ w 62 = 1 := Control.Proofs.control_bits holds 3
  have b4 : w 63 = 0 ∨ w 63 = 1 := Control.Proofs.control_bits holds 4
  have b5 : w 64 = 0 ∨ w 64 = 1 := Control.Proofs.control_bits holds 5
  have b7 : w 66 = 0 ∨ w 66 = 1 := Control.Proofs.control_bits holds 7
  have total := Control.Proofs.opcode_exclusivity (by decide) holds
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Variables.operations, Fin.getElem_fin] at total
  norm_num at total
  have v0 := bit_val b0
  have v1 := bit_val b1
  have v2 := bit_val b2
  have v3 := bit_val b3
  have v4 := bit_val b4
  have v5 := bit_val b5
  have v7 := bit_val b7
  have one : (1 : ZMod babyBearModulus).val = 1 := ZMod.val_one'' (by decide)
  have zeroOf {x : ZMod babyBearModulus} (bit : x = 0 ∨ x = 1) (value : x.val = 0) : x = 0 :=
    bit.resolve_right (fun h => by rw [h, one] at value; exact absurd value (by decide))
  have oneOf {x : ZMod babyBearModulus} (bit : x = 0 ∨ x = 1) (value : x.val = 1) : x = 1 :=
    bit.resolve_left (fun h => by rw [h] at value; simp at value)
  by_cases s0 : (w 59).val = 1
  · exact Or.inr ⟨0, oneOf b0 s0, by simp; omega⟩
  by_cases s1 : (w 60).val = 1
  · exact Or.inr ⟨1, oneOf b1 s1, by simp; omega⟩
  by_cases s2 : (w 61).val = 1
  · exact Or.inr ⟨2, oneOf b2 s2, by simp; omega⟩
  by_cases s3 : (w 62).val = 1
  · exact Or.inr ⟨3, oneOf b3 s3, by simp; omega⟩
  by_cases s4 : (w 63).val = 1
  · exact Or.inr ⟨4, oneOf b4 s4, by simp; omega⟩
  by_cases s5 : (w 64).val = 1
  · exact Or.inr ⟨5, oneOf b5 s5, by simp; omega⟩
  by_cases s7 : (w 66).val = 1
  · exact Or.inr ⟨6, oneOf b7 s7, by simp; omega⟩
  refine Or.inl ⟨?_, by omega⟩
  intro i
  fin_cases i
  · exact zeroOf (x := w 59) b0 (by omega)
  · exact zeroOf (x := w 60) b1 (by omega)
  · exact zeroOf (x := w 61) b2 (by omega)
  · exact zeroOf (x := w 62) b3 (by omega)
  · exact zeroOf (x := w 63) b4 (by omega)
  · exact zeroOf (x := w 64) b5 (by omega)
  · exact zeroOf (x := w 66) b7 (by omega)

/-- A bigint row computes the spec's `bigintOp` for the control word `x12` it reads (any high limb): the written limbs
    are the result `mod 2²⁵⁶`, x12's written low limb the flag, its high limb zero. -/
theorem row_operation {w : Nat → ZMod babyBearModulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    {x12 : RV.Word} (low : x12.toNat % 65536 = (w 55).val) :
    x12.toNat % 2 ^ 16 < 256 ∧ ∃ r f, RV.Delegation.bigintOp (x12 &&& 0xbf#32) (x12.getLsbD 6)
        (value (limbs w Variables.leftLimbs)) (value (limbs w Variables.rightLimbs)) = some (r, f) ∧
      value (output w).result = r % 2 ^ 256 ∧ (w 57).val = (if f then 1 else 0) ∧ (w 58).val = 0 := by
  have small : (w 55).val < 256 := (mask_columns holds).2
  obtain ⟨guard, opWord, carryBit⟩ := control_byte low small
  refine ⟨guard, ?_⟩
  rw [opWord, carryBit]
  have effects := Native.Proofs.arithmetic_effects holds
  have ranges := source_ranges (by decide) holds
  have leftBound : ∀ i : Fin 16, (limbs w Variables.leftLimbs)[i] < 65536 := by
    intro i; simpa [limbs, limbBase] using (ranges i).1
  have rightBound : ∀ i : Fin 16, (limbs w Variables.rightLimbs)[i] < 65536 := by
    intro i; simpa [limbs, limbBase] using (ranges i).2
  have resultBound : ∀ i : Fin 16, (output w).result[i] < 65536 := by
    intro i; simpa [output, limbs, limbBase] using written_limb_bounds (by decide) holds i
  have resultLt := value_lt resultBound
  simp only [output] at resultLt ⊢
  have carry : (w 65).val = 0 ∨ (w 65).val = 1 := bit_val (Control.Proofs.control_bits holds 6)
  have cle : (w 65).val ≤ 1 := by omega
  have cBool : ((w 65).val == 1).toNat = (w 65).val := by rcases carry with c | c <;> simp [c]
  rcases control_cases holds with ⟨empty, m⟩ | ⟨chosen, sel, m⟩
  · obtain ⟨zero, low57, high58⟩ := empty_writes holds empty
    rw [m, (bigintOp_control cle _ _).1]
    refine ⟨_, _, rfl, ?_, by simp [low57], by simp [high58]⟩
    have limbsZero : limbs w Variables.writtenLimbs = Vector.replicate 16 0 := by
      apply Vector.ext
      intro i hi
      simpa [output, limbs] using zero ⟨i, hi⟩
    rw [limbsZero]
    simp [value]
  · fin_cases chosen
    -- ADD
    · have m' : (w 55).val = 1 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, controlLe, controlHi, sum⟩ := effects.1 .add sel
      simp only [additiveInput, output, cBool] at sum controlLe controlHi
      have split := carry_split resultLt controlLe sum
      simp only [decide_eq_true_eq]
      exact ⟨split.1, split.2, controlHi⟩
    -- SUB
    · have m' : (w 55).val = 2 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, controlLe, controlHi, sum⟩ := effects.1 .sub sel
      simp only [additiveInput, output, cBool] at sum controlLe controlHi
      have split := borrow_split (a := value (limbs w Variables.leftLimbs))
        (b := value (limbs w Variables.rightLimbs) + (w 65).val) resultLt controlLe (by rw [← Nat.add_assoc]; exact sum)
      simp only [decide_eq_true_eq]
      exact ⟨split.1, split.2, controlHi⟩
    -- SUB_NEGATE
    · have m' : (w 55).val = 4 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, controlLe, controlHi, sum⟩ := effects.1 .reverseSub sel
      simp only [additiveInput, output, cBool] at sum controlLe controlHi
      have split := borrow_split (a := value (limbs w Variables.rightLimbs))
        (b := value (limbs w Variables.leftLimbs) + (w 65).val) resultLt controlLe (by rw [← Nat.add_assoc]; exact sum)
      simp only [decide_eq_true_eq]
      exact ⟨split.1, split.2, controlHi⟩
    -- MUL_LOW
    · have m' : (w 55).val = 8 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.2.2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, product, control⟩ := effects.2.2 .low sel
      simp only [multiplicationInput, output] at product control
      obtain ⟨lo, hi⟩ := Word.mk.inj control
      simp only [decide_eq_true_eq]
      exact ⟨product, lo, hi⟩
    -- MUL_HIGH
    · have m' : (w 55).val = 16 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.2.2.2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, product, control⟩ := effects.2.2 .high sel
      simp only [multiplicationInput, output] at product control
      obtain ⟨lo, hi⟩ := Word.mk.inj control
      rw [product] at resultLt ⊢
      exact ⟨(Nat.mod_eq_of_lt resultLt).symm, lo, hi⟩
    -- EQ
    · have m' : (w 55).val = 32 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.2.2.2.2.1]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨same, control⟩ := effects.2.1 sel
      simp only [equalityInput, output] at same control
      obtain ⟨lo, hi⟩ := Word.mk.inj control
      have iff : limbs w Variables.leftLimbs = limbs w Variables.rightLimbs ↔
          value (limbs w Variables.leftLimbs) = value (limbs w Variables.rightLimbs) :=
        ⟨fun h => by rw [h], value_injective leftBound rightBound⟩
      refine ⟨by rw [same, Nat.mod_eq_of_lt (value_lt leftBound)], ?_, hi⟩
      rw [lo]
      simp only [iff, decide_eq_true_eq]
    -- MEMCOPY
    · have m' : (w 55).val = 128 + 64 * (w 65).val := by norm_num at m; omega
      rw [m', (bigintOp_control cle _ _).2.2.2.2.2.2.2]
      refine ⟨_, _, rfl, ?_⟩
      obtain ⟨_, controlLe, controlHi, sum⟩ := effects.1 .copy sel
      simp only [additiveInput, output, cBool] at sum controlLe controlHi
      have split := carry_split resultLt controlLe sum
      simp only [decide_eq_true_eq]
      exact ⟨split.1, split.2, controlHi⟩

end Airbender.Bigint.Proofs
