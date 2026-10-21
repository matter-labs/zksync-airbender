import Slop.RV.Step
import Human.Theorems

/-! Link check: the image bytes at each function's address are the code words the proofs use.
Checked in one pass over the image (`linkedFrom`, fast in the kernel), then turned into `CodeAt`. -/

set_option linter.unusedSimpArgs false

namespace RV

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

theorem codeAt_of_bytes {bytes : Array (BitVec 8)} {s : State} (himg : ImageLoaded bytes s) (a : Nat)
    (code : List Word) (hb : a + 4 * code.length ≤ bytes.size) (hs : bytes.size < 2 ^ 32)
    (h : (bytes.toList.drop a).take (4 * code.length) = bytesOf code) :
    CodeAt s (BitVec.ofNat 32 a) code := by
  intro i hi
  have key : ∀ j < 4, s.mem (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) =
      write s.mem (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i)) code[i] 4
        (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j) := by
    intro j hj
    rw [write4_at _ _ _ j hj]
    have hidx : (BitVec.ofNat 32 a + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 j).toNat = a + (4 * i + j) := by
      bv_omega
    have hlt : a + (4 * i + j) < bytes.size := by omega
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

/-- The little-endian bytes of a list of words, word by word (linear to evaluate). -/
def bytesOfW : List Word → List (BitVec 8)
  | [] => []
  | w :: ws => w.setWidth 8 :: (w >>> 8).setWidth 8 :: (w >>> 16).setWidth 8 :: (w >>> 24).setWidth 8 :: bytesOfW ws

theorem bytesOfW_length (code : List Word) : (bytesOfW code).length = 4 * code.length := by
  induction code with
  | nil => rfl
  | cons w ws ih => simp only [bytesOfW, List.length_cons, ih]; omega

theorem bytesOfW_eq (code : List Word) : bytesOfW code = bytesOf code := by
  apply List.ext_getElem
  · simp [bytesOfW_length, bytesOf]
  · intro k h1 h2
    simp only [bytesOf, List.getElem_ofFn]
    induction code generalizing k with
    | nil => simp [bytesOfW] at h1
    | cons w ws ih =>
      simp only [bytesOfW]
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with h | h | h | h | h
      · subst h; simp <;> rfl
      · subst h; simp <;> rfl
      · subst h; simp <;> rfl
      · subst h; simp <;> rfl
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
        simp only [List.getElem_cons_succ]
        rw [ih j (by simp only [bytesOfW_length, List.length_cons] at h1 ⊢; omega)
          (by simp only [bytesOf, List.length_ofFn, List.length_cons] at h2 ⊢; omega)]
        simp only [show (j + 4) / 4 = j / 4 + 1 by omega, show (j + 4) % 4 = j % 4 by omega, List.getElem_cons_succ]

/-- The pieces `(a, code)`, by increasing `a`, are at their addresses in the byte list `l` (which starts at address
`pos`): one pass over the image, which the kernel evaluates once for all the code. -/
def linkedFrom : List (BitVec 8) → Nat → List (Nat × List Word) → Bool
  | _, _, [] => true
  | l, pos, (a, code) :: rest =>
    decide (pos ≤ a) && decide ((l.drop (a - pos)).take (4 * code.length) = bytesOfW code) &&
      linkedFrom (l.drop (a - pos)) a rest

theorem linkedFrom_mem : ∀ (l : List (BitVec 8)) (pos : Nat) (layout : List (Nat × List Word)),
    linkedFrom l pos layout = true → ∀ p ∈ layout,
      pos ≤ p.1 ∧ (l.drop (p.1 - pos)).take (4 * p.2.length) = bytesOfW p.2
  | _, _, [], _, _, hp => nomatch hp
  | l, pos, (a, code) :: rest, h, p, hp => by
    simp only [linkedFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpa, hc⟩, hr⟩ := h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hpa, hc⟩
    · obtain ⟨h1, h2⟩ := linkedFrom_mem _ a rest hr p hp
      refine ⟨by omega, ?_⟩
      rwa [List.drop_drop, show a - pos + (p.1 - a) = p.1 - pos by omega] at h2

/-- Piece `i` of a layout checked by `linkedFrom` is code at its address. -/
theorem codeAt_of_linked {bytes : Array (BitVec 8)} {s : State} (himg : ImageLoaded bytes s)
    (hs : bytes.size < 2 ^ 32) {layout : List (Nat × List Word)} (h : linkedFrom bytes.toList 0 layout = true)
    {a : Nat} {code : List Word} (i : Nat) (hi : layout[i]? = some (a, code)) : CodeAt s (BitVec.ofNat 32 a) code := by
  obtain ⟨-, hc⟩ := linkedFrom_mem _ 0 layout h _ (List.mem_of_getElem? hi)
  simp only [Nat.sub_zero] at hc
  have hl := congrArg List.length hc
  simp only [List.length_take, List.length_drop, Array.length_toList, bytesOfW_length] at hl
  rcases Nat.eq_zero_or_pos code.length with h0 | h0
  · intro i hi; omega
  · exact codeAt_of_bytes himg a code (by omega) hs (by rw [hc, bytesOfW_eq])

end RV
