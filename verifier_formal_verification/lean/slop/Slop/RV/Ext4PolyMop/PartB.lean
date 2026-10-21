import Slop.RV.Ext4Call
import Slop.RV.Coeffs4
import Slop.RV.Ext4PolyMop.Block

/-! `ext4_poly` with the field opcodes, after `ext4_horner` returns: block B (`out = to_u32(e)`, saved registers
back) and the `ret`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

namespace PolyMB
abbrev rSp : Region := ⟨2, 0, 48, 16⟩
abbrev rOut : Region := ⟨9, 0, 16, 4⟩
end PolyMB
open PolyMB

theorem word47 (h : 47 < Code.ext4_poly_mop.length) : Code.ext4_poly_mop[47]'h = 0x00008067#32 := rfl

/-- From the return of `ext4_horner` (frame `sp - 48` as part A left it, `e` at `sp - 28`): back at `ra` with
`out = to_u32(e)`, the callee-saved registers restored, memory changed only at `out`. -/
theorem poly_mop_part_b (A : Word) (s S2 : State) (hpc : S2.pc = A + 120#32)
    (hcode : CodeAt S2 A Code.ext4_poly_mop) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 192 ≤ ROM_END)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 112 ≤ (s.getReg 2#5).toNat)
    (hspr : (s.getReg 2#5).toNat ≤ RAM_END)
    (ho4 : (s.getReg 10#5).toNat % 4 = 0) (hos : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat)
    (hor : (s.getReg 10#5).toNat + 16 ≤ RAM_END) (hra : (s.getReg 1#5).toNat % 4 = 0)
    (h2 : S2.getReg 2#5 = s.getReg 2#5 + 4294967248#32) (h9 : S2.getReg 9#5 = s.getReg 10#5)
    (hr : ∀ r : Reg, 18 ≤ r.toNat → r.toNat ≤ 27 → S2.getReg r = s.getReg r)
    (k1 : read S2.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5)
    (k8 : read S2.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5)
    (k9 : read S2.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5) :
    ∃ n T, run n S2 = some T ∧ T.pc = s.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 16 ≤ a.toNat → T.mem a = S2.mem a) ∧
      canon4 T.mem (s.getReg 10#5) ∧
      limbsAt T.mem (s.getReg 10#5) = e4At S2.mem (s.getReg 2#5 + 4294967268#32) := by
  have hlen : Code.ext4_poly_mop.length = 48 := by decide +kernel
  simp only [ROM_END, RAM_END] at *
  have h2n : (S2.getReg 2#5).toNat = (s.getReg 2#5).toNat - 48 := by rw [h2]; bv_omega
  have h9n : (S2.getReg 9#5).toNat = (s.getReg 10#5).toNat := by rw [h9]
  have hcB : CodeAt S2 (A + BitVec.ofNat 32 (4 * 30)) ((Code.ext4_poly_mop.drop 30).take 17) :=
    codeAt_take (codeAt_drop hcode 30 (by rw [hlen]; omega)) 17
  obtain ⟨S3, hrun3, hpc3, hrel3, hrom3, hout3, hfr3⟩ := block_from _ PolyMB.instrs PolyMB.σ S2 _ [rSp, rOut]
    [(rSp, rOut)] PolyMB.dec PolyMB.run (by rw [hpc]) (by bv_omega) (by simp [hlen, ROM_END]; bv_omega) hcB
    (by sym_side) (by sym_side) (by decide +kernel)
  rw [List.length_take, List.length_drop, hlen, show min 17 (48 - 30) = 17 from rfl] at hrun3 hpc3
  -- loads of block B, read back
  have ld : ∀ i (k : Word), i < PolyMB.σ.pool.len → nodeAt PolyMB.σ.pool i = .load 4 true 2 k →
      PolyMB.σ.pool.val (ctxOf S2) i = read S2.mem (s.getReg 2#5 + (4294967248#32 + k)) 4 := fun i k hi h => by
    rw [load_val _ _ PolyMB.run S2 i 2 k true (by decide) hi h, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2,
      BitVec.add_assoc]
  have l41 := ld 41 44#32 (by decide +kernel) (by decide +kernel)
  have l42 := ld 42 40#32 (by decide +kernel) (by decide +kernel)
  have l43 := ld 43 36#32 (by decide +kernel) (by decide +kernel)
  simp only [BitVec.reduceAdd] at l41 l42 l43
  -- registers after block B
  have rv : ∀ (r : Reg) (i : Nat), (PolyMB.σ.reg r).val = i → S3.getReg r = PolyMB.σ.pool.val (ctxOf S2) i :=
    fun r i h => by rw [(hrel3.2.2.1 r).2, h]
  have r1 : S3.getReg 1#5 = s.getReg 1#5 := by rw [rv 1#5 41 (by decide +kernel), l41, k1]
  -- `ret`
  have hw : read S3.mem S3.pc 4 = 0x00008067#32 := by
    rw [read_congr S3.mem S2.mem _ 4 (fun j hj => hrom3 _ (by rw [hpc3]; simp only [ROM_END]; bv_omega)), hpc3]
    have := hcode 47 (by rw [hlen]; omega)
    rw [word47] at this
    rw [show A + BitVec.ofNat 32 (4 * 30) + BitVec.ofNat 32 (4 * 17) = A + BitVec.ofNat 32 (4 * 47) by
      rw [BitVec.add_assoc]; rfl]
    exact this
  have hstep : step S3 = some ((S3.setPC (S3.getReg 1#5)).setReg 0#5 (S3.pc + 4)) := by
    rw [step_fetch S3 _ (by rw [hpc3]; bv_omega) (by rw [hpc3]; simp only [ROM_END]; bv_omega) hw,
      show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl, Option.bind_some,
      exec_jalr0 S3 _ _ (by rw [r1]; exact hra)]
  refine ⟨17 + 1, _, by rw [run_add, hrun3, Option.bind_some, run_succ, hstep]; rfl,
    by simp only [jump_pc, State.setReg]; exact r1, ?_, ?_, ?_⟩
  · -- callee-saved registers
    intro i hi
    rw [r_set, jump_r]
    split
    · next h => subst h; rfl
    · split
      · next h => exact absurd h (by rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide)
      · rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
        · rw [hrel3.reg_addr _ PolyMB.run 2#5 2 48#32 (by decide) (by decide +kernel) (by decide +kernel),
            show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; bv_omega
        · rw [rv _ 42 (by decide +kernel), l42, k8]
        · rw [rv _ 43 (by decide +kernel), l43, k9]
        all_goals
          rw [hrel3.reg_same _ PolyMB.run _ (by decide +kernel)]
          exact hr _ (by decide) (by decide)
  · intro a ha
    simp only [set_mem, jump_mem]
    apply hfr3 [⟨9, 0, 16, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR
    simp only [List.mem_singleton] at hR
    subst hR
    simp only [Region.Outside, h9n]
    omega
  · simp only [set_mem, jump_mem]
    -- `out_k = mop.mul(e_k, 1)`
    have o : ∀ (k : Word) (i j : Nat) (kk : Word), outOK PolyMB.σ [rSp, rOut] [(rSp, rOut)] 9 k = true →
        outNode PolyMB.σ 9 k = i → nodeAt PolyMB.σ.pool i = .mop .mul j 33 0 →
        nodeAt PolyMB.σ.pool j = .load 4 true 2 kk → j < PolyMB.σ.pool.len → i < PolyMB.σ.pool.len →
        read S3.mem (s.getReg 10#5 + k) 4 =
          mopVal .mul (read S2.mem (s.getReg 2#5 + (4294967248#32 + kk)) 4) 1#32 0#32 :=
      fun k i j kk h hn hi hj hjl hil => by
        rw [← h9, hout3 9 k (by decide) h, hn, (nodeAt_spec (ctxOf S2) _ PolyMB.wf i hil).2, hi, ← ld j kk hjl hj]
        simp only [Node.eval]
        rw [(nodeAt_spec (ctxOf S2) _ PolyMB.wf 33 (by decide +kernel)).2,
          (nodeAt_spec (ctxOf S2) _ PolyMB.wf 0 (by decide +kernel)).2]
        rfl
    have o0 := o 0#32 34 32 20#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have o1 := o 4#32 36 35 24#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have o2 := o 8#32 38 37 28#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have o3 := o 12#32 40 39 32#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    simp only [show s.getReg 10#5 + 0#32 = s.getReg 10#5 by simp, BitVec.reduceAdd] at o0 o1 o2 o3
    refine ⟨⟨by rw [o0]; exact mopVal_lt _ _ _ _ nofun, by rw [o1]; exact mopVal_lt _ _ _ _ nofun,
      by rw [o2]; exact mopVal_lt _ _ _ _ nofun, by rw [o3]; exact mopVal_lt _ _ _ _ nofun⟩, ?_⟩
    simp only [limbsAt, e4At, e4, o0, o1, o2, o3, mul_one_val, BitVec.add_assoc, BitVec.reduceAdd]

end RV
