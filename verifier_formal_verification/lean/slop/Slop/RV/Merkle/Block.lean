import Slop.RV.Blake.Impl
import Slop.Sym.Meta
import Slop.RV.Code.merkle_step

/-! `merkle_step`, its straight-line middle (words 9 … 70, after the side branch has put the left half's pointer in
`a1` and the right half's in `a2`): the block `left ‖ right` at `st + 64`, the configured IV at `st`, the counter
zero, `ra` and `s0` restored, `a1 = 64` (bytes), `a2 = 1` (last block), `sp` back. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

sym_run MStep := (Code.merkle_step.drop 9).take 62

namespace MStepR
abbrev rStk : Region := ⟨2, 0, 16, 16⟩
abbrev rIV : Region := ⟨10, 0, 32, 4⟩
abbrev rL : Region := ⟨10, 64, 96, 4⟩
abbrev rR : Region := ⟨10, 96, 132, 4⟩
abbrev rA1 : Region := ⟨11, 0, 32, 4⟩
abbrev rA2 : Region := ⟨12, 0, 32, 4⟩
end MStepR
open MStepR

/-- The block, from a state `S` at word 9 of `merkle_step` at `A`: the evaluator at `a0` (4-aligned, in RAM, above
the 16-byte frame at `sp`), the halves at `a1`, `a2` (8 words each, in RAM; `a2`'s apart from the left half's
destination). -/
theorem merkle_block (S : State) (A : Word) (hal : A.toNat % 4 = 0)
    (hrom : A.toNat + 4 * Code.merkle_step.length ≤ ROM_END) (hcode : CodeAt S A Code.merkle_step)
    (hpc : S.pc = A + 36#32)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : ROM_END ≤ (S.getReg 2#5).toNat)
    (hst : (S.getReg 10#5).toNat % 4 = 0) (hst1 : (S.getReg 2#5).toNat + 16 ≤ (S.getReg 10#5).toNat)
    (hst2 : (S.getReg 10#5).toNat + 132 ≤ RAM_END)
    (h11 : (S.getReg 11#5).toNat % 4 = 0) (h11a : ROM_END ≤ (S.getReg 11#5).toNat)
    (h11b : (S.getReg 11#5).toNat + 32 ≤ RAM_END)
    (h12 : (S.getReg 12#5).toNat % 4 = 0) (h12a : ROM_END ≤ (S.getReg 12#5).toNat)
    (h12b : (S.getReg 12#5).toNat + 32 ≤ RAM_END)
    (h12d : (S.getReg 12#5).toNat + 32 ≤ (S.getReg 10#5).toNat + 64 ∨
      (S.getReg 10#5).toNat + 96 ≤ (S.getReg 12#5).toNat) :
    ∃ S', run 62 S = some S' ∧ S'.pc = A + 284#32 ∧
      S'.getReg 10#5 = S.getReg 10#5 ∧ S'.getReg 11#5 = 64#32 ∧ S'.getReg 12#5 = 1#32 ∧
      S'.getReg 1#5 = read S.mem (S.getReg 2#5 + 12#32) 4 ∧ S'.getReg 8#5 = read S.mem (S.getReg 2#5 + 8#32) 4 ∧
      S'.getReg 2#5 = S.getReg 2#5 + 16#32 ∧
      (∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S'.getReg r = S.getReg r) ∧
      wordsAt S'.mem (S.getReg 10#5) 8 = Vector.ofFn configuredIV ∧
      wordsAt S'.mem (S.getReg 10#5 + 64#32) 16 =
        wordsAt S.mem (S.getReg 11#5) 8 ++ wordsAt S.mem (S.getReg 12#5) 8 ∧
      read S'.mem (S.getReg 10#5 + 128#32) 4 = 0#32 ∧
      (∀ a : Word, a.toNat < (S.getReg 10#5).toNat ∨ (S.getReg 10#5).toNat + 132 ≤ a.toNat → S'.mem a = S.mem a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  have hlen : Code.merkle_step.length = 72 := rfl
  rw [hlen] at hrom
  simp only [ROM_END, RAM_END] at *
  have hc : CodeAt S (A + BitVec.ofNat 32 (4 * 9)) ((Code.merkle_step.drop 9).take 62) :=
    codeAt_take (codeAt_drop hcode 9 (by rw [hlen]; omega)) 62
  obtain ⟨S', hrun, hpc', hrel, hromB, hout, hfr⟩ := block_from _ MStep.instrs MStep.σ S _
    [rStk, rIV, rL, rR, rA1, rA2] [(rA2, rL), (rStk, rIV), (rStk, rL), (rStk, rR)]
    MStep.dec MStep.run (by rw [hpc]) (by bv_omega) (by simp [hlen, ROM_END]; bv_omega) hc (by simp (disch := decide) only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, RV.Sym.Region.Holds, RV.Sym.initPool_val, RV.ROM_END, RV.RAM_END]; omega) (by sym_side)
    (by decide +kernel)
  have rs : ∀ r : Reg, (MStep.σ.reg r).val = r.toNat → S'.getReg r = S.getReg r := fun r h =>
    hrel.reg_same _ MStep.run r h
  have rl : ∀ (r : Reg) (b : Nat) (k : Word), b < 32 → (MStep.σ.reg r).val < MStep.σ.pool.len →
      nodeAt MStep.σ.pool (MStep.σ.reg r).val = .load 4 true b k →
      S'.getReg r = read S.mem (S.getReg (BitVec.ofNat 5 b) + k) 4 := fun r b k hb hi hn => by
    rw [(hrel.2.2.1 r).2]; exact load_val _ _ MStep.run S _ b k true hb hi hn
  have stc : ∀ (k w : Word), outOK MStep.σ [rStk, rIV, rL, rR, rA1, rA2]
      [(rA2, rL), (rStk, rIV), (rStk, rL), (rStk, rR)] 10 k = true →
      outNode MStep.σ 10 k < MStep.σ.pool.len → nodeAt MStep.σ.pool (outNode MStep.σ 10 k) = .const w →
      read S'.mem (S.getReg 10#5 + k) 4 = w := fun k w h hi hc => by
    rw [hout 10 k (by decide) h]; exact val_const MStep.wf _ _ w hi hc
  have stl : ∀ (k : Word) (b : Nat) (k' : Word), outOK MStep.σ [rStk, rIV, rL, rR, rA1, rA2]
      [(rA2, rL), (rStk, rIV), (rStk, rL), (rStk, rR)] 10 k = true → b < 32 →
      outNode MStep.σ 10 k < MStep.σ.pool.len → nodeAt MStep.σ.pool (outNode MStep.σ 10 k) = .load 4 true b k' →
      read S'.mem (S.getReg 10#5 + k) 4 = read S.mem (S.getReg (BitVec.ofNat 5 b) + k') 4 := fun k b k' h hb hi hn => by
    rw [hout 10 k (by decide) h]; exact load_val _ _ MStep.run S _ b k' true hb hi hn
  refine ⟨S', hrun, by rw [hpc']; simp only [List.length_take, List.length_drop, hlen]; bv_omega, rs _ (by decide +kernel), hrel.reg_cst _ _ (by decide +kernel),
    hrel.reg_cst _ _ (by decide +kernel), rl _ 2 12#32 (by decide) (by decide +kernel) (by decide +kernel),
    rl _ 2 8#32 (by decide) (by decide +kernel) (by decide +kernel),
    hrel.reg_addr _ MStep.run 2#5 2 16#32 (by decide) (by decide +kernel) (by decide +kernel),
    fun r hr h2 h8 => ?_, ?_, ?_, ?_, fun a ha => ?_, hromB⟩
  · rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      first | exact rs _ (by decide +kernel) | exact absurd rfl h2 | exact absurd rfl h8
  · apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    all_goals exact stc _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel +revert)
  · apply Vector.ext; intro i hi
    rw [Vector.getElem_append]
    simp only [wordsAt, Vector.getElem_ofFn, BitVec.add_assoc]
    interval_cases i
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    · exact stl _ 11 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
    all_goals exact stl _ 12 _ (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  · rw [← BitVec.add_zero (S.getReg 10#5 + 128#32), BitVec.add_assoc]
    exact stc _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · apply hfr [⟨10, 0, 132, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside]; omega

end RV
