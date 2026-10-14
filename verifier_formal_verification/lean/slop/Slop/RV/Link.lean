import Slop.RV.Step
import Human.Theorems

/-! Link check: the image bytes at each function's address are the code words the proofs use.
Checked as one list equality per block (fast in the kernel), then turned into `CodeAt`. -/

set_option linter.unusedSimpArgs false

namespace RV

/-- Memory holding exactly the image bytes (0 elsewhere). -/
def imageMem (a : Word) : BitVec 8 := if h : a.toNat < Image.bytes.size then Image.bytes[a.toNat] else 0

/-- The little-endian bytes of a list of words. -/
def bytesOf (code : List Word) : List (BitVec 8) :=
  List.ofFn fun k : Fin (4 * code.length) =>
    (code[k.val / 4]'(by have := k.isLt; omega) >>> (8 * (k.val % 4))).setWidth 8

theorem write4_at (m : Word → BitVec 8) (b v : Word) (j : Nat) (hj : j < 4) :
    write m b v 4 (b + BitVec.ofNat 32 j) = (v >>> (8 * j)).setWidth 8 := by
  have e1 : b ≠ b + 1#32 := by bv_omega
  have e2 : b ≠ b + 1#32 + 1#32 := by bv_omega
  have e3 : b ≠ b + 1#32 + 1#32 + 1#32 := by bv_omega
  have e4 : b + 1#32 ≠ b + 1#32 + 1#32 := by bv_omega
  have e5 : b + 1#32 ≠ b + 1#32 + 1#32 + 1#32 := by bv_omega
  have e6 : b + 1#32 + 1#32 ≠ b + 1#32 + 1#32 + 1#32 := by bv_omega
  simp only [write]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h
  · rw [show b + BitVec.ofNat 32 0 = b by bv_omega]
    simp [e1, e2, e3]
  · rw [show b + BitVec.ofNat 32 1 = b + 1 by bv_omega]
    simp [e1.symm, e4, e5]
  · rw [show b + BitVec.ofNat 32 2 = b + 1 + 1 by bv_omega]
    simp [e2.symm, e4.symm, e6]
  · rw [show b + BitVec.ofNat 32 3 = b + 1 + 1 + 1 by bv_omega]
    simp

theorem codeAt_of_bytes {s : State} (himg : ImageLoaded s) (a : Nat) (code : List Word)
    (hb : a + 4 * code.length ≤ Image.bytes.size) (hs : Image.bytes.size < 2 ^ 32)
    (h : (Image.bytes.toList.drop a).take (4 * code.length) = bytesOf code) :
    CodeAt s (BitVec.ofNat 32 a) code := by
  intro i hi
  have key : ∀ j < 4, s.mem (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) =
      write s.mem (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) code[i] 4
        (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) := by
    intro j hj
    rw [write4_at _ _ _ j hj]
    have hidx : (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j).toNat = a + (4 * i + j) := by
      bv_omega
    have hlt : a + (4 * i + j) < Image.bytes.size := by omega
    have e := himg (a + (4 * i + j)) hlt
    rw [show BitVec.ofNat 32 (a + (4 * i + j)) = BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j
      by bv_omega] at e
    rw [e]
    have hk : 4 * i + j < 4 * code.length := by omega
    have := congrArg (fun l => l[4 * i + j]?) h
    simp only [List.getElem?_take, hk, ite_true, List.getElem?_drop, bytesOf, List.getElem?_ofFn, dite_true,
      Array.getElem?_toList, Array.getElem?_eq_getElem hlt, Option.some.injEq] at this
    rw [this]
    simp only [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega]
  rw [read_congr _ (write s.mem _ code[i] 4) _ 4 (fun j hj => by simpa using key j hj), read_write_same4]

end RV
