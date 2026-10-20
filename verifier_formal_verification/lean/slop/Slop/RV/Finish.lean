import Slop.RV.Halt
import Slop.RV.CopyRun
import Slop.RV.Code.finish_success
import Slop.RV.Code.finish_success_extended
import Slop.Block.Block
import Slop.RV.FinishRuns

/-! riscv_common's `zksync_os_finish_success` (the output protocol), at any address. -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 400000

-- words 0 … 28 (straight-line; word 29 is the call of `zksync_os_finish_success_extended`)

/-- riscv_common's `zksync_os_finish_success` (at `A`), called with `a0` pointing to the 8 output words (in RAM, at
or above `sp`): builds the 16-word output array (the 8 words, then 8 zeros) in its frame and jumps to
`zksync_os_finish_success_extended` (linked right after it, at `A + 0x78`) with `a0` pointing to it. -/
theorem finish_success_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 0x78 ≤ 4194304) (S : State)
    (hc1 : CodeAt S A Code.finish_success)
    (hpc : S.pc = A) (P : Word) (h10 : S.getReg 10#5 = P) (w0 w1 w2 w3 w4 w5 w6 w7 : Word)
    (h0 : read S.mem P 4 = w0) (h1 : read S.mem (P + 4#32) 4 = w1)
    (h2 : read S.mem (P + 8#32) 4 = w2) (h3 : read S.mem (P + 12#32) 4 = w3)
    (h4 : read S.mem (P + 16#32) 4 = w4) (h5 : read S.mem (P + 20#32) 4 = w5)
    (h6 : read S.mem (P + 24#32) 4 = w6) (h7 : read S.mem (P + 28#32) 4 = w7)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 128 ≤ (S.getReg 2#5).toNat)
    (hP : (S.getReg 2#5).toNat ≤ P.toNat) (hP4 : P.toNat % 4 = 0) (hP2 : P.toNat + 32 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 0x78#32 ∧ S'.getReg 2#5 = S.getReg 2#5 + 4294967216#32 ∧
      S'.getReg 10#5 = S.getReg 2#5 + 4294967224#32 ∧
      read S'.mem (S.getReg 2#5 + 4294967224#32) 4 = w0 ∧ read S'.mem (S.getReg 2#5 + 4294967228#32) 4 = w1 ∧
      read S'.mem (S.getReg 2#5 + 4294967232#32) 4 = w2 ∧ read S'.mem (S.getReg 2#5 + 4294967236#32) 4 = w3 ∧
      read S'.mem (S.getReg 2#5 + 4294967240#32) 4 = w4 ∧ read S'.mem (S.getReg 2#5 + 4294967244#32) 4 = w5 ∧
      read S'.mem (S.getReg 2#5 + 4294967248#32) 4 = w6 ∧ read S'.mem (S.getReg 2#5 + 4294967252#32) 4 = w7 ∧
      read S'.mem (S.getReg 2#5 + 4294967256#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967260#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967264#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967268#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967272#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967276#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967280#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967284#32) 4 = 0 ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  have hL : Code.finish_success.length = 30 := rfl
  have hrom : A.toNat + 4 * Code.finish_success.length ≤ ROM_END := by simp only [ROM_END, hL]; omega
  have hPn : (S.getReg 10#5).toNat = P.toNat := by rw [h10]
  obtain ⟨S1, hrun1, hpc1, -, hrel, hrom1, hout, -⟩ := block_at _ 0 29 FinSucc.instrs FinSucc.σ S A
    [⟨2, -80, 0, 16⟩, ⟨10, 0, 32, 4⟩] [(⟨10, 0, 32, 4⟩, ⟨2, -80, 0, 16⟩)] FinSucc.dec FinSucc.run (by decide)
    (by rw [hpc]; bv_omega) hA hrom hc1 (by sym_side) (by sym_side) (by decide +kernel)
  have hj := run_jal hc1 hA hrom hrom1 29 _ rfl hpc1 1#5 4#32 rfl (A + 0x78#32) (by bv_omega) (by bv_omega)
  -- the array: word `k` of the frame is the word at `a0 + k'`, or 0
  have W : ∀ (k k' v : Word), outOK FinSucc.σ [⟨2, -80, 0, 16⟩, ⟨10, 0, 32, 4⟩] [(⟨10, 0, 32, 4⟩, ⟨2, -80, 0, 16⟩)]
      2 k = true → outNode FinSucc.σ 2 k < FinSucc.σ.pool.len →
      nodeAt FinSucc.σ.pool (outNode FinSucc.σ 2 k) = .load 4 true 10 k' → read S.mem (P + k') 4 = v →
      read S1.mem (S.getReg 2#5 + k) 4 = v := fun k k' v hok hi hn hv => by
    rw [← hv, ← h10]; exact out_load _ FinSucc.run hout 2 k 10 k' (by decide) (by decide) hok hi hn
  have Z : ∀ k : Word, outOK FinSucc.σ [⟨2, -80, 0, 16⟩, ⟨10, 0, 32, 4⟩] [(⟨10, 0, 32, 4⟩, ⟨2, -80, 0, 16⟩)]
      2 k = true → outNode FinSucc.σ 2 k < FinSucc.σ.pool.len →
      nodeAt FinSucc.σ.pool (outNode FinSucc.σ 2 k) = .const 0 → read S1.mem (S.getReg 2#5 + k) 4 = 0 :=
    fun k hok hi hn => out_const FinSucc.wf hout 2 k 0 (by decide) hok hi hn
  refine ⟨29 + 1, _, run_trans hrun1 hj, rfl,
    by rw [jal_getReg _ _ _ _ (by decide)]
       exact hrel.reg_addr _ FinSucc.run 2#5 2 _ (by decide) (by decide +kernel) (by decide +kernel),
    by rw [jal_getReg _ _ _ _ (by decide)]
       exact hrel.reg_addr _ FinSucc.run 10#5 2 _ (by decide) (by decide +kernel) (by decide +kernel), ?_⟩
  simp only [jal_mem]
  refine ⟨W _ 0#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by rw [BitVec.add_zero]; exact h0),
    W _ 4#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h1,
    W _ 8#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h2,
    W _ 12#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h3,
    W _ 16#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h4,
    W _ 20#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h5,
    W _ 24#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h6,
    W _ 28#32 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) h7,
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    Z _ (by decide +kernel) (by decide +kernel) (by decide +kernel), hrom1⟩
end RV
