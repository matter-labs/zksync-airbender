import Slop.RV.Ext4Call
import Slop.RV.Coeffs4
import Slop.RV.Ext4Poly.BValues

/-! `ext4_poly` in plain Rust, after `ext4_horner` returns: block B (`out = to_u32(e)`, saved registers back) and
the `ret`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

namespace PolyB
abbrev rSp : Region := ⟨2, 0, 64, 16⟩
abbrev rOut : Region := ⟨9, 0, 16, 4⟩
end PolyB
open PolyB

theorem word139 (h : 139 < Code.ext4_poly.length) : Code.ext4_poly[139]'h = 0x00008067#32 := rfl

/-- From the return of `ext4_horner` (frame `sp - 64` as part A left it, `e` at `sp - 44` canonical): back at `ra`
with `out = to_u32(e)`, the callee-saved registers restored, memory changed only at `out`. -/
theorem poly_part_b (A : Word) (s S2 : State) (hpc : S2.pc = A + 348#32) (hcode : CodeAt S2 A Code.ext4_poly)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 560 ≤ ROM_END)
    (hsp16 : (s.getReg 2#5).toNat % 16 = 0) (hspl : ROM_END + 192 ≤ (s.getReg 2#5).toNat)
    (hspr : (s.getReg 2#5).toNat ≤ RAM_END)
    (ho4 : (s.getReg 10#5).toNat % 4 = 0) (hos : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat)
    (hor : (s.getReg 10#5).toNat + 16 ≤ RAM_END) (hra : (s.getReg 1#5).toNat % 4 = 0)
    (h2 : S2.getReg 2#5 = s.getReg 2#5 + 4294967232#32) (h9 : S2.getReg 9#5 = s.getReg 10#5)
    (h18 : S2.getReg 18#5 = 2013265920#32) (h19 : S2.getReg 19#5 = 2013265921#32)
    (h20 : S2.getReg 20#5 = 2013265919#32)
    (hr : ∀ r : Reg, 22 ≤ r.toNat → r.toNat ≤ 27 → S2.getReg r = s.getReg r)
    (k1 : read S2.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5)
    (k8 : read S2.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5)
    (k9 : read S2.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5)
    (k18 : read S2.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5)
    (k19 : read S2.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5)
    (k20 : read S2.mem (s.getReg 2#5 + 4294967272#32) 4 = s.getReg 20#5)
    (k21 : read S2.mem (s.getReg 2#5 + 4294967268#32) 4 = s.getReg 21#5)
    (hcanon : canon4 S2.mem (s.getReg 2#5 + 4294967252#32)) :
    ∃ n T, run n S2 = some T ∧ T.pc = s.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 16 ≤ a.toNat → T.mem a = S2.mem a) ∧
      canon4 T.mem (s.getReg 10#5) ∧
      limbsAt T.mem (s.getReg 10#5) = e4At S2.mem (s.getReg 2#5 + 4294967252#32) := by
  have hlen : Code.ext4_poly.length = 140 := by decide +kernel
  simp only [ROM_END, RAM_END] at *
  have h2n : (S2.getReg 2#5).toNat = (s.getReg 2#5).toNat - 64 := by rw [h2]; bv_omega
  have h9n : (S2.getReg 9#5).toNat = (s.getReg 10#5).toNat := by rw [h9]
  have hcB : CodeAt S2 (A + BitVec.ofNat 32 (4 * 87)) ((Code.ext4_poly.drop 87).take 52) :=
    codeAt_take (codeAt_drop hcode 87 (by rw [hlen]; omega)) 52
  obtain ⟨S3, hrun3, hpc3, hrel3, hrom3, hout3, hfr3⟩ := block_from _ PolyB.instrs PolyB.σ S2 _ [rSp, rOut]
    [(rSp, rOut)] PolyB.dec PolyB.run (by rw [hpc]) (by bv_omega) (by simp [hlen, ROM_END]; bv_omega) hcB
    (by sym_side) (by sym_side) (by decide +kernel)
  rw [List.length_take, List.length_drop, hlen, show min 52 (140 - 87) = 52 from rfl] at hrun3 hpc3
  -- loads of block B, read back
  have ld : ∀ i (k : Word), i < PolyB.σ.pool.len → nodeAt PolyB.σ.pool i = .load 4 true 2 k →
      PolyB.σ.pool.val (ctxOf S2) i = read S2.mem (s.getReg 2#5 + (4294967232#32 + k)) 4 := fun i k hi h => by
    rw [load_val _ _ PolyB.run S2 i 2 k true (by decide) hi h, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2,
      BitVec.add_assoc]
  have l73 := ld 73 60#32 (by decide +kernel) (by decide +kernel)
  have l74 := ld 74 56#32 (by decide +kernel) (by decide +kernel)
  have l75 := ld 75 52#32 (by decide +kernel) (by decide +kernel)
  have l76 := ld 76 48#32 (by decide +kernel) (by decide +kernel)
  have l77 := ld 77 44#32 (by decide +kernel) (by decide +kernel)
  have l78 := ld 78 40#32 (by decide +kernel) (by decide +kernel)
  have l79 := ld 79 36#32 (by decide +kernel) (by decide +kernel)
  have l32 := ld 32 20#32 (by decide +kernel) (by decide +kernel)
  have l33 := ld 33 24#32 (by decide +kernel) (by decide +kernel)
  have l34 := ld 34 28#32 (by decide +kernel) (by decide +kernel)
  have l35 := ld 35 32#32 (by decide +kernel) (by decide +kernel)
  simp only [BitVec.reduceAdd] at l73 l74 l75 l76 l77 l78 l79 l32 l33 l34 l35
  -- registers after block B
  have rv : ∀ (r : Reg) (i : Nat), (PolyB.σ.reg r).val = i → S3.getReg r = PolyB.σ.pool.val (ctxOf S2) i :=
    fun r i h => by rw [(hrel3.2.2.1 r).2, h]
  have r1 : S3.getReg 1#5 = s.getReg 1#5 := by rw [rv 1#5 73 (by decide +kernel), l73, k1]
  -- `ret`
  have hw : read S3.mem S3.pc 4 = 0x00008067#32 := by
    rw [read_congr S3.mem S2.mem _ 4 (fun j hj => hrom3 _ (by rw [hpc3]; simp only [ROM_END]; bv_omega)), hpc3]
    have := hcode 139 (by rw [hlen]; omega)
    rw [word139] at this
    rw [show A + BitVec.ofNat 32 (4 * 87) + BitVec.ofNat 32 (4 * 52) = A + BitVec.ofNat 32 (4 * 139) by
      rw [BitVec.add_assoc]; rfl]
    exact this
  have hstep : step S3 = some ((S3.setPC (S3.getReg 1#5)).setReg 0#5 (S3.pc + 4)) := by
    rw [step_fetch S3 _ (by rw [hpc3]; bv_omega) (by rw [hpc3]; simp only [ROM_END]; bv_omega) hw,
      show decode 0x00008067#32 = some (.jalr 0#5 1#5 0#32) from rfl, Option.bind_some,
      exec_jalr0 S3 _ _ (by rw [r1]; exact hra)]
  refine ⟨52 + 1, _, by rw [run_add, hrun3, Option.bind_some, run_succ, hstep]; rfl,
    by simp only [jump_pc, State.setReg]; exact r1, ?_, ?_, ?_⟩
  · -- callee-saved registers
    intro i hi
    rw [r_set, jump_r]
    split
    · next h => subst h; rfl
    · split
      · next h => exact absurd h (by rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide)
      · rcases calleeSaved_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
        · rw [hrel3.reg_addr _ PolyB.run 2#5 2 64#32 (by decide) (by decide +kernel) (by decide +kernel),
            show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; bv_omega
        · rw [rv _ 74 (by decide +kernel), l74, k8]
        · rw [rv _ 75 (by decide +kernel), l75, k9]
        · rw [rv _ 76 (by decide +kernel), l76, k18]
        · rw [rv _ 77 (by decide +kernel), l77, k19]
        · rw [rv _ 78 (by decide +kernel), l78, k20]
        · rw [rv _ 79 (by decide +kernel), l79, k21]
        all_goals
          rw [hrel3.reg_same _ PolyB.run _ (by decide +kernel)]
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
    have o : ∀ k, outOK PolyB.σ [rSp, rOut] [(rSp, rOut)] 9 k = true →
        read S3.mem (s.getReg 10#5 + k) 4 = PolyB.σ.pool.val (ctxOf S2) (outNode PolyB.σ 9 k) :=
      fun k h => by rw [← h9]; exact hout3 9 k (by decide) h
    have o69 := o 0#32 (by decide +kernel)
    have o70 := o 4#32 (by decide +kernel)
    have o71 := o 8#32 (by decide +kernel)
    have o72 := o 12#32 (by decide +kernel)
    rw [show outNode PolyB.σ 9 0#32 = 69 by decide +kernel, show s.getReg 10#5 + 0#32 = s.getReg 10#5 by simp] at o69
    rw [show outNode PolyB.σ 9 4#32 = 70 by decide +kernel] at o70
    rw [show outNode PolyB.σ 9 8#32 = 71 by decide +kernel] at o71
    rw [show outNode PolyB.σ 9 12#32 = 72 by decide +kernel] at o72
    simp only [canon4, BitVec.add_assoc, BitVec.reduceAdd] at hcanon
    obtain ⟨b69, b70, b71, b72, v69, v70, v71, v72⟩ := PolyB.values (ctxOf S2) h18 h19 h20
      (by rw [l32]; exact hcanon.1) (by rw [l33]; exact hcanon.2.1) (by rw [l34]; exact hcanon.2.2.1)
      (by rw [l35]; exact hcanon.2.2.2)
    refine ⟨⟨by rw [o69]; exact b69, by rw [o70]; exact b70, by rw [o71]; exact b71, by rw [o72]; exact b72⟩, ?_⟩
    simp only [limbsAt, e4At, e4, o69, o70, o71, o72, v69, v70, v71, v72, l32, l33, l34, l35, BitVec.add_assoc,
      BitVec.reduceAdd]

end RV
