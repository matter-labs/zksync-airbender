import Slop.RV.Ext4Call
import Slop.RV.Code.ext4_horner
import Slop.Block.Block

/-! The epilogue of `ext4_horner`, shared by the `n = 0` path and the loop exit: one symbolic block (words 26 … 40)
and `ret`. -/

namespace RV
open Spec RV.Sym RV.Block
set_option maxHeartbeats 400000

sym_run HEpi := (Code.ext4_horner.drop 26).take 15

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
  have e2 : S.getReg (BitVec.ofNat 5 2) = sp0 + 4294967248#32 := h2
  have e9 : S.getReg (BitVec.ofNat 5 9) = out := h9
  have h2n : (S.getReg (BitVec.ofNat 5 2)).toNat = sp0.toNat - 48 := by rw [e2]; bv_omega
  have h9n : (S.getReg (BitVec.ofNat 5 9)).toNat = out.toNat := by rw [e9]
  have hc : CodeAt S (A + BitVec.ofNat 32 (4 * 26)) ((Code.ext4_horner.drop 26).take 15) :=
    codeAt_take (codeAt_drop hcode 26 (by simp only [Code.ext4_horner, List.length_cons, List.length_nil]; omega)) 15
  -- a frame slot, as the block addresses it
  have fr : ∀ k c v : Word, 4294967248#32 + k = c → read S.mem (sp0 + c) 4 = v →
      read S.mem (S.getReg (BitVec.ofNat 5 2) + k) 4 = v := fun k c v hk h => by rw [e2, BitVec.add_assoc, hk, h]
  have hL : ((Code.ext4_horner.drop 26).take 15).length = 15 := rfl
  obtain ⟨T, hrun, hpcT, hrel, -, hout, hfr⟩ := block_ret 26 15 HEpi.instrs HEpi.σ
    [⟨2, 0, 48, 4⟩, ⟨9, 0, 16, 4⟩] [(⟨9, 0, 16, 4⟩, ⟨2, 0, 48, 4⟩)] HEpi.dec HEpi.run (by decide)
    (by rw [hpc]; try rfl) (by bv_omega) (by rw [show Code.ext4_horner.length = 42 from rfl]; simp only [ROM_END]; omega) hcode (by decide +kernel)
    (by sym_side) (by sym_side) (by decide +kernel)
    (fun S' h => by
      rw [Rel.reg_load _ HEpi.run h 1#5 2 44#32 (by decide) (by decide +kernel) (by decide +kernel), fr _ _ _ (by decide) h1]
      exact hra)
  have rl : ∀ (r : Reg) (k c v : Word), 4294967248#32 + k = c → (HEpi.σ.reg r).val < HEpi.σ.pool.len →
      nodeAt HEpi.σ.pool (HEpi.σ.reg r).val = .load 4 true 2 k → read S.mem (sp0 + c) 4 = v →
      T.getReg r = v := fun r k c v hk hi hn h => by rw [Rel.reg_load _ HEpi.run hrel r 2 k (by decide) hi hn, fr _ _ _ hk h]
  -- `out[k] = acc[k]`
  have ok : ∀ k : Word, outOK HEpi.σ [⟨2, 0, 48, 4⟩, ⟨9, 0, 16, 4⟩] [(⟨9, 0, 16, 4⟩, ⟨2, 0, 48, 4⟩)] 9 k = true →
      outNode HEpi.σ 9 k < HEpi.σ.pool.len → nodeAt HEpi.σ.pool (outNode HEpi.σ 9 k) = .load 4 true 2 (8#32 + k) →
      read T.mem (out + k) 4 = read S.mem (sp0 + 4294967256#32 + k) 4 := fun k h hi hn => by
    rw [← e9, out_load _ HEpi.run hout 9 k 2 _ (by decide) (by decide) h hi hn, e2, ← BitVec.add_assoc,
      BitVec.add_assoc sp0]; simp only [BitVec.reduceAdd]
  have o0 := ok 0#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have o4 := ok 4#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have o8 := ok 8#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have o12 := ok 12#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [BitVec.add_zero, BitVec.add_zero] at o0
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at o4 o8 o12
  refine ⟨_, T, hrun, ?_, ?_, rl _ 40#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h8,
    rl _ 36#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h9', rl _ 32#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h18,
    rl _ 28#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h19, rl _ 24#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h20,
    regs_same_range _ HEpi.run hrel 21 27 (by decide +kernel), ?_, ?_, ?_⟩
  · rw [hpcT, rl _ 44#32 _ _ (by decide) (by decide +kernel) (by decide +kernel) h1]
  · rw [hrel.reg_addr _ HEpi.run 2#5 2 48#32 (by decide) (by decide +kernel) (by decide +kernel), e2,
      BitVec.add_assoc]; simp only [BitVec.reduceAdd, BitVec.add_zero]
  · simp only [canon4, BitVec.add_assoc, BitVec.reduceAdd, o0, o4, o8, o12]; exact id
  · simp only [e4At, BitVec.add_assoc, BitVec.reduceAdd, o0, o4, o8, o12]
  · intro a ha
    exact out_frame hfr ⟨9, 0, 16, 1⟩ (by decide +kernel) (by decide)
      (by simp only [Region.Holds, initPool_val _ _ (by decide : 9 < 32), h9n, ROM_END, RAM_END]; omega) a
      (by simp only [Region.Outside, h9n]; omega)
end RV
