import Slop.RV.Halt
import Slop.RV.CopyRun
import Slop.RV.Code.finish_success_extended
import Slop.Block.Block
import Slop.RV.FinishRuns

/-! riscv_common's `zksync_os_finish_success_extended`, at any address: the outputs land in `x10 … x25`. -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 400000

/-- riscv_common's `zksync_os_finish_success_extended` (at `A`), with `a0` pointing to the 16-word output array
(at `sp + 8`, as `zksync_os_finish_success` calls it): loads the words into `x10 … x25` and reaches its final
self-jump (`A + 0x80`). -/
theorem finish_extended_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 0x84 ≤ 4194304) (S : State)
    (hc : CodeAt S A Code.finish_success_extended)
    (hpc : S.pc = A) (h10 : S.getReg 10#5 = S.getReg 2#5 + 8#32)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Word)
    (hm0 : read S.mem (S.getReg 2#5 + 8#32) 4 = r0) (hm1 : read S.mem (S.getReg 2#5 + 12#32) 4 = r1) (hm2 : read S.mem (S.getReg 2#5 + 16#32) 4 = r2) (hm3 : read S.mem (S.getReg 2#5 + 20#32) 4 = r3) (hm4 : read S.mem (S.getReg 2#5 + 24#32) 4 = r4) (hm5 : read S.mem (S.getReg 2#5 + 28#32) 4 = r5) (hm6 : read S.mem (S.getReg 2#5 + 32#32) 4 = r6) (hm7 : read S.mem (S.getReg 2#5 + 36#32) 4 = r7) (hm8 : read S.mem (S.getReg 2#5 + 40#32) 4 = r8) (hm9 : read S.mem (S.getReg 2#5 + 44#32) 4 = r9) (hm10 : read S.mem (S.getReg 2#5 + 48#32) 4 = r10) (hm11 : read S.mem (S.getReg 2#5 + 52#32) 4 = r11) (hm12 : read S.mem (S.getReg 2#5 + 56#32) 4 = r12) (hm13 : read S.mem (S.getReg 2#5 + 60#32) 4 = r13) (hm14 : read S.mem (S.getReg 2#5 + 64#32) 4 = r14) (hm15 : read S.mem (S.getReg 2#5 + 68#32) 4 = r15)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 64 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat + 128 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 0x80#32 ∧ S'.getReg 10#5 = r0 ∧ S'.getReg 11#5 = r1 ∧ S'.getReg 12#5 = r2 ∧ S'.getReg 13#5 = r3 ∧ S'.getReg 14#5 = r4 ∧ S'.getReg 15#5 = r5 ∧ S'.getReg 16#5 = r6 ∧ S'.getReg 17#5 = r7 ∧ S'.getReg 18#5 = r8 ∧ S'.getReg 19#5 = r9 ∧ S'.getReg 20#5 = r10 ∧ S'.getReg 21#5 = r11 ∧ S'.getReg 22#5 = r12 ∧ S'.getReg 23#5 = r13 ∧ S'.getReg 24#5 = r14 ∧ S'.getReg 25#5 = r15 ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  have hL : Code.finish_success_extended.length = 33 := by decide +kernel
  have h10n : (S.getReg 10#5).toNat = (S.getReg 2#5).toNat + 8 := by rw [h10]; bv_omega
  obtain ⟨S3, hrun3, hpc3, -, hrel3, hrom3, hout3, -⟩ := block_at Code.finish_success_extended 0 32 FinExt.instrs
    FinExt.σ S A [⟨2, -48, 0, 16⟩, ⟨10, 0, 64, 4⟩] [(⟨2, -48, 0, 16⟩, ⟨10, 0, 64, 4⟩)]
    (by rw [List.drop_zero]; exact FinExt.dec) FinExt.run (by decide) (by rw [hpc]; simp) hA
    (by rw [hL]; simp only [ROM_END]; omega) hc (by sym_side) (by sym_side) (by decide +kernel)
  refine ⟨32, S3, hrun3, by rw [hpc3],?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 10#5 10 0#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm0
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 11#5 10 4#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm1
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 12#5 10 8#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm2
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 13#5 10 12#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm3
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 14#5 10 16#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm4
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 15#5 10 20#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm5
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 16#5 10 24#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm6
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 17#5 10 28#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm7
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 18#5 10 32#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm8
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 19#5 10 36#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm9
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 20#5 10 40#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm10
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 21#5 10 44#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm11
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 22#5 10 48#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm12
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 23#5 10 52#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm13
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 24#5 10 56#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm14
  · rw [Rel.reg_load FinExt.instrs FinExt.run hrel3 25#5 10 60#32 (by decide) (by decide +kernel)
      (by decide +kernel), h10, BitVec.add_assoc]
    simp only [BitVec.reduceAdd]; exact hm15
  · exact hrom3
end RV
