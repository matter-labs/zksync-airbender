import Slop.RV.Ext4Call
import Slop.RV.Code.ext4_horner

/-! The epilogue of `ext4_horner`, shared by the `n = 0` path and the loop exit. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- The epilogue of `ext4_horner` (from `+0x68`): copies `acc` (at `sp0 - 40`) to `out` (`s1`), restores the saved
registers from the frame and returns. -/
theorem horner_epi (A sp0 out ra v8 v9 v18 v19 v20 : Word) (S : State) (hA : A.toNat % 4 = 0)
    (hAr : A.toNat + 168 ≤ 4194304) (hcode : CodeAt S A Code.ext4_horner) (hpc : S.pc = A + 104#32)
    (h2 : S.getReg 2#5 = sp0 + 4294967248#32) (h9 : S.getReg 9#5 = out)
    (hsp : sp0.toNat % 16 = 0) (hlo : 4194304 + 48 ≤ sp0.toNat) (hhi : sp0.toNat ≤ 1073741824)
    (ho4 : out.toNat % 4 = 0) (hos : sp0.toNat ≤ out.toNat) (hor : out.toNat + 16 ≤ 1073741824)
    (hra : ra.toNat % 4 = 0)
    (h1 : read S.mem (sp0 + 4294967292#32) 4 = ra) (h8 : read S.mem (sp0 + 4294967288#32) 4 = v8)
    (h9' : read S.mem (sp0 + 4294967284#32) 4 = v9) (h18 : read S.mem (sp0 + 4294967280#32) 4 = v18)
    (h19 : read S.mem (sp0 + 4294967276#32) 4 = v19) (h20 : read S.mem (sp0 + 4294967272#32) 4 = v20) :
    ∃ m S', run m S = some S' ∧ S'.pc = ra ∧ S'.getReg 2#5 = sp0 ∧ S'.getReg 8#5 = v8 ∧ S'.getReg 9#5 = v9 ∧
      S'.getReg 18#5 = v18 ∧ S'.getReg 19#5 = v19 ∧ S'.getReg 20#5 = v20 ∧
      (∀ i : Reg, 21 ≤ i.toNat → i.toNat ≤ 27 → S'.getReg i = S.getReg i) ∧
      (canon4 S.mem (sp0 + 4294967256#32) → canon4 S'.mem out) ∧
      e4At S'.mem out = e4At S.mem (sp0 + 4294967256#32) ∧
      (∀ a : Word, a.toNat < out.toNat ∨ out.toNat + 16 ≤ a.toNat → S'.mem a = S.mem a) := by
  rv_code_facts_range hcode Code.ext4_horner 26 42
  rv_steps 16 with hpc, h2, h9, h1, h8, h9', h18, h19, h20
  rv_ret
  refine ⟨by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2
    rcases (by bv_omega : i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5) with
      h|h|h|h|h|h|h <;> subst h <;> rv_regs
  · simp only [canon4]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
      read_write_off0l, read_write_disjoint, BitVec.add_assoc]
    exact id
  · simp only [e4At]
    simp (disch := rv_disch) only [rv_state, BitVec.reduceAdd, read_write_same4, read_write_off, read_write_off0r,
      read_write_off0l, read_write_disjoint, BitVec.add_assoc]
  · intro a ha
    simp (disch := rv_disch) only [rv_state, write_outside]
end RV
