import Slop.RV.PolyLoop

/-! `poly_eval` — shared definitions and the `n = 0` path. `poly_eval(coeffs, n, x)` at any address, for any table of `n` field elements: prologue (or the `n = 0` exit),
then the loop lemma. -/

namespace RV

/-- Precondition of `poly_eval`: `a0` points to the table `C` (word-aligned, in ROM), `a1 = C.length`,
`a2 = x ≤ P`. -/
def polyPre (C : List Word) : State → Prop := fun s =>
  CodeAt s (s.getReg 10) C ∧ s.getReg 11 = BitVec.ofNat 32 C.length ∧ (s.getReg 10).toNat + 4 * C.length ≤ 4194304 ∧
    (s.getReg 10).toNat % 4 = 0 ∧ (s.getReg 12).toNat ≤ P

def polyPost (C : List Word) : State → State → Prop := fun s s' =>
  (s'.getReg 10).toNat ≤ P ∧ (s'.getReg 10).toNat % P = polyW C (s.getReg 12).toNat % P

theorem ofNat_shl2 (n : Nat) (h : n < 2 ^ 30) : BitVec.ofNat 32 n <<< 2 = BitVec.ofNat 32 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

set_option maxHeartbeats 1000000 in
theorem poly_eval_empty (A : Word) (hA : 256 ≤ A.toNat) (C : List Word) (hn : C.length = 0)
    (hC : ∀ i (h : i < C.length), C[i].toNat ≤ P) :
    ImplementsAtPre A Code.poly_eval [(A + 4294967236#32, Code.mul_mod), (A + 4294967040#32, Code.add_mod)] 48
      (polyPre C) (polyPost C) := by
  intro s hentry hcallees hcall hpre
  have hmul : CodeAt s (A + 4294967236#32) Code.mul_mod := hcallees (A + 4294967236#32, Code.mul_mod) (by simp)
  have hadd : CodeAt s (A + 4294967040#32) Code.add_mod := hcallees (A + 4294967040#32, Code.add_mod) (by simp)
  clear hcallees
  obtain ⟨hcoef, ha1, hT, hT4, hx⟩ := hpre
  simp only [BitVec.ofNat_eq_ofNat] at hcoef ha1 hT hT4 hx
  have hcode : CodeAt s A Code.poly_eval := hentry ▸ hcall.1
  rw [Call, hentry] at hcall
  rv_start Code.poly_eval hcall
  have hA4 : A.toNat % 4 = 0 := hpc
  -- n = 0: `beq` to the exit, return 0
  have hC0 : C = [] := List.eq_nil_of_length_eq_zero hn
  subst hC0
  rv_steps 17 with hentry, ha1
  rv_ret
  refine ⟨by rv_regs, ⟨by rv_regs; simp, by rv_regs; simp [polyW]⟩, ?_, ?_⟩
  · intro i hi
    rcases calleeSaved_cases i hi with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      (rv_step_simp with ha1)
  · intro a ha
    simp (disch := rv_disch) only [set_mem, next_mem, store_mem, jump_mem, write_outside]

end RV
