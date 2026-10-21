import Slop.RV.FsCheck.Blocks
import Human.SpecExt4

/-! The values `fs_check`'s blocks compute: the reduction of a word into BabyBear (two branch-free conditional
subtractions, as rustc compiles `from_raw_repr_with_reduction`), the challenge (block A), the comparison
(block B: zero iff the claim is the computed value). -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 400000

/-- One conditional subtraction of `p`, branch-free: `x + (-(k < x) &&& m)` with `k = p - 1`, `m = -p`. -/
def csub (k m x : Word) : Word := alu .add x (alu .and m (alu .sub 0 (alu .sltu k x)))

/-- Reduction of a word into BabyBear (`2^32 < 3p`: two subtractions suffice). -/
def red (x : Word) : Word := csub 0x78000000#32 0x87ffffff#32 (csub 0x78000000#32 0x87ffffff#32 x)

theorem csub_eq (k m x : Word) : csub k m x = if k.ult x then x + m else x := by
  unfold csub alu
  by_cases h : k.ult x <;> simp [h]
  rw [show (4294967295#32 : Word) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes]

theorem red_eq (x : Word) : red x = BitVec.ofNat 32 (x.toNat % BabyBearP) := by
  simp only [red, csub_eq, BabyBearP]
  split_ifs <;> simp only [BitVec.ult, decide_eq_true_eq] at * <;> bv_omega

theorem red_lt (x : Word) : (red x).toNat < BabyBearP := by
  rw [red_eq, BitVec.toNat_ofNat]; simp only [BabyBearP]; omega

theorem red_bb (x : Word) : ((red x).toNat : Spec.F) = (x.toNat : Spec.F) := by
  rw [red_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [BabyBearP]; omega)]
  exact ZMod.natCast_mod _ _

set_option hygiene false in
local notation "A[" i "]" => Pool.val c FsA.σ.pool i
set_option hygiene false in
local notation "B[" i "]" => Pool.val c FsB.σ.pool i

/-- Block A: the challenge words, `red` of the four words at `a0`. -/
theorem fsA_z (c : Ctx) :
    A[54] = red (read c.m (c.env 10) 4) ∧ A[57] = red (read c.m (c.env 10 + 4#32) 4) ∧
    A[71] = red (read c.m (c.env 10 + 8#32) 4) ∧ A[72] = red (read c.m (c.env 10 + 12#32) 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sym_unfold <;> simp only [sext_word, ite_true, BitVec.add_zero] <;> rfl

/-- Block B (with `s2 = p - 1`, `s3 = -p` from block A): the difference is zero iff each computed limb (at `sp + 24`)
is `red` of the claimed one (at `s1`). -/
theorem fsB_diff (c : Ctx) (h18 : c.env 18 = 0x78000000#32) (h19 : c.env 19 = 0x87ffffff#32) :
    B[78] = 0#32 ↔
      read c.m (c.env 2 + 24#32) 4 = red (read c.m (c.env 9) 4) ∧
      read c.m (c.env 2 + 28#32) 4 = red (read c.m (c.env 9 + 4#32) 4) ∧
      read c.m (c.env 2 + 32#32) 4 = red (read c.m (c.env 9 + 8#32) 4) ∧
      read c.m (c.env 2 + 36#32) 4 = red (read c.m (c.env 9 + 12#32) 4) := by
  sym_unfold
  simp only [sext_word, ite_true, BitVec.add_zero, h18, h19]
  simp only [alu, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, red, csub]
  constructor
  · rintro ⟨⟨a, b⟩, d, e⟩; exact ⟨a, b, d, e⟩
  · rintro ⟨a, b, d, e⟩; exact ⟨⟨a, b⟩, d, e⟩

end RV
