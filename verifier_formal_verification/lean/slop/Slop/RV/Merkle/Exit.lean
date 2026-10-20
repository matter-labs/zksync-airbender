import Slop.RV.Tactic
import Slop.RV.Input
import Slop.RV.CopyRun
import Slop.RV.Stuck
import Slop.RV.FsCheck.Blocks
import Slop.RV.Code.merkle_check
import Human.SpecMerkle
import Slop.RV.Merkle.MFrame
import Slop.Block.Out
import Slop.Block.Tail
import Slop.Block.ExitRuns

/-! `merkle_check`, the end (from word 68): the node in `MERKLE.state` against the root (in `s9 … s2`), then either
the epilogue and `ret` (they match) or `zksync_os_finish_error` (they differ: the run gets stuck). -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- `zksync_os_finish_error` (its code at `Aerr`, 16 free bytes below `sp`): the run reaches its
`csrrw x0, cycle, x0`. -/
theorem finish_error_stuck (S : State) (Aerr : Word) (hpc : S.pc = Aerr) (hAerr : Aerr.toNat % 4 = 0)
    (hAerrr : Aerr.toNat + 24 ≤ ROM_END) (herr : CodeAt S Aerr Code.finish_error)
    (hsp1 : ROM_END + 16 ≤ (S.getReg 2#5).toNat) (hsp2 : (S.getReg 2#5).toNat ≤ RAM_END)
    (hsp3 : (S.getReg 2#5).toNat % 16 = 0) :
    ∃ n T, run n S = some T ∧ AtFinishError T := by
  have hL : Code.finish_error.length = 6 := by decide +kernel
  simp only [ROM_END, RAM_END] at hAerrr hsp1 hsp2
  obtain ⟨S6, hrun6, hpc6, -, -, hrom6, -, -⟩ := block_at Code.finish_error 0 4 FinErr.instrs FinErr.σ S Aerr
    [⟨2, -16, 0, 16⟩] [] (by rw [List.drop_zero]; exact FinErr.dec) FinErr.run (by decide) (by rw [hpc]; simp)
    hAerr (by rw [hL]; simp only [ROM_END]; omega) herr (by sym_side) (by simp) (by decide +kernel)
  refine ⟨4, S6, hrun6, by rw [hpc6]; bv_omega, by rw [hpc6]; simp only [ROM_END]; bv_omega, ?_⟩
  rw [read_congr S6.mem S.mem _ 4 (fun j hj => hrom6 _ (by rw [hpc6]; simp only [ROM_END]; bv_omega)), hpc6]
  exact herr 4 (by rw [hL]; decide)

/-- The eight words `merkle_check` writes into `MERKLE.state` (word 7 first) read back. -/
theorem readWords_merkle (m : Word → BitVec 8) (v0 v1 v2 v3 v4 v5 v6 v7 : Word) :
    readWords (write (write (write (write (write (write (write (write m 20975900#32 v7 4) 20975896#32 v6 4)
      20975892#32 v5 4) 20975888#32 v4 4) 20975884#32 v3 4) 20975880#32 v2 4) 20975876#32 v1 4) 20975872#32 v0 4)
      MERKLE 8 = #v[v0, v1, v2, v3, v4, v5, v6, v7] := by
  apply Vector.ext; intro i hi
  simp only [readWords, Vector.getElem_ofFn]
  interval_cases i <;> simp (disch := decide) only [BitVec.reduceAdd, Nat.reduceMul, MERKLE, read_write_disjoint,
    read_write_same4] <;> rfl

/-- The 13 words the prologue saves below `sp` do not change a word read at or above `sp`. -/
theorem read_above_frame (m : Word → BitVec 8) (sp b v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : Word) (hb : sp.toNat ≤ b.toNat)
    (hsp : 52 ≤ sp.toNat) (hb2 : b.toNat + 4 ≤ 2 ^ 32) :
    read (write (write (write (write (write (write (write (write (write (write (write (write
      (write m (sp + 4294967292#32) v0 4) (sp + 4294967288#32) v1 4) (sp + 4294967284#32) v2 4)
      (sp + 4294967280#32) v3 4) (sp + 4294967276#32) v4 4) (sp + 4294967272#32) v5 4)
      (sp + 4294967268#32) v6 4) (sp + 4294967264#32) v7 4) (sp + 4294967260#32) v8 4)
      (sp + 4294967256#32) v9 4) (sp + 4294967252#32) v10 4) (sp + 4294967248#32) v11 4)
      (sp + 4294967244#32) v12 4) b 4 = read m b 4 := by
  repeat rw [read_write_disjoint (h := Or.inl (by bv_omega)) (ha := by bv_omega) (hc := hb2)]

/-- `MERKLE`'s eight words equal `root` iff the computed comparison (the root registers against the words at
`s10 + 256`, `s10 = MERKLE - 0x100`) holds. -/
theorem exit_mroot (E : State) (root : Vector Word 8) (h26 : E.getReg 26#5 = 0x1401000#32)
    (r0 : E.getReg 25#5 = root[0]) (r1 : E.getReg 24#5 = root[1]) (r2 : E.getReg 23#5 = root[2])
    (r3 : E.getReg 22#5 = root[3]) (r4 : E.getReg 20#5 = root[4]) (r5 : E.getReg 21#5 = root[5])
    (r6 : E.getReg 19#5 = root[6]) (r7 : E.getReg 18#5 = root[7]) :
    readWords E.mem MERKLE 8 = root ↔
      (E.getReg 25#5 = read E.mem (E.getReg 26#5 + 256#32) 4 ∧ E.getReg 24#5 = read E.mem (E.getReg 26#5 + 260#32) 4 ∧
       E.getReg 23#5 = read E.mem (E.getReg 26#5 + 264#32) 4 ∧ E.getReg 22#5 = read E.mem (E.getReg 26#5 + 268#32) 4 ∧
       E.getReg 20#5 = read E.mem (E.getReg 26#5 + 272#32) 4 ∧ E.getReg 21#5 = read E.mem (E.getReg 26#5 + 276#32) 4 ∧
       E.getReg 19#5 = read E.mem (E.getReg 26#5 + 280#32) 4 ∧ E.getReg 18#5 = read E.mem (E.getReg 26#5 + 284#32) 4) := by
  have mw : ∀ i (h : i < 8), read E.mem (MERKLE + BitVec.ofNat 32 (4 * i)) 4 = (readWords E.mem MERKLE 8)[i] :=
    fun i h => by simp [readWords]
  rw [h26, r0, r1, r2, r3, r4, r5, r6, r7]
  have m0 := mw 0 (by decide); have m1 := mw 1 (by decide); have m2 := mw 2 (by decide)
  have m3 := mw 3 (by decide); have m4 := mw 4 (by decide); have m5 := mw 5 (by decide)
  have m6 := mw 6 (by decide); have m7 := mw 7 (by decide)
  constructor
  · intro h
    rw [← h]
    exact ⟨m0.symm, m1.symm, m2.symm, m3.symm, m4.symm, m5.symm, m6.symm, m7.symm⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    apply Vector.ext; intro i hi
    interval_cases i
    · exact m0.trans h0.symm
    · exact m1.trans h1.symm
    · exact m2.trans h2.symm
    · exact m3.trans h3.symm
    · exact m4.trans h4.symm
    · exact m5.trans h5.symm
    · exact m6.trans h6.symm
    · exact m7.trans h7.symm

/-- A word of the frame's memory read back: `read` of an address at `sp + k`, `16 ≤ k`, `k + 4 ≤ 96`, agrees in two
memories that agree on `[sp + 16, sp + 96)`. -/
theorem exit_read_frame (m m' : Word → BitVec 8) (sp k : Word) (hk : 16 ≤ k.toNat) (hk2 : k.toNat + 4 ≤ 96)
    (hsp : sp.toNat + 96 ≤ 2 ^ 32) (h : ∀ a : Word, sp.toNat + 16 ≤ a.toNat → a.toNat < sp.toNat + 96 → m' a = m a) :
    read m' (sp + k) 4 = read m (sp + k) 4 :=
  read_congr2 m m' _ _ 4 (fun j hj => h _ (by bv_omega) (by bv_omega))

/-- One callee-saved register restored from the frame (a load at `sp + k`, `sp` as at the start). -/
theorem exit_restore (S7 S8 E s0 : State) (r : Reg) (k k' : Word) (hk : 16 ≤ k.toNat) (hk2 : k.toNat + 4 ≤ 96)
    (hsp : (E.getReg 2#5).toNat + 96 ≤ 2 ^ 32) (hsp7 : S7.getReg 2#5 = E.getReg 2#5)
    (hfr : ∀ a : Word, (E.getReg 2#5).toNat + 16 ≤ a.toNat → a.toNat < (E.getReg 2#5).toNat + 96 → S7.mem a = E.mem a)
    (hload : S8.getReg r = read S7.mem (S7.getReg 2#5 + k) 4)
    (hkk : E.getReg 2#5 + k = s0.getReg 2#5 + k') (hv : read E.mem (s0.getReg 2#5 + k') 4 = s0.getReg r) :
    S8.getReg r = s0.getReg r := by
  rw [hload, hsp7, exit_read_frame E.mem S7.mem (E.getReg 2#5) k hk hk2 hsp hfr, hkk, hv]

theorem mc_exit (s0 E : State) (A : Word) (F len : Nat) (root : Vector Word 8) (rest : List Word)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 111 + 0x21c + 24 ≤ ROM_END)
    (hcode : CodeAt E A Code.merkle_check) (herr : CodeAt E (A + 0x3d4#32) Code.finish_error)
    (hpc : E.pc = A + 272#32) (fr : MFrame s0 F len root E)
    (hin : E.input = rest) (hF : 112 ≤ F) (hsp0 : ROM_END + F ≤ (s0.getReg 2#5).toNat)
    (hsp0' : (s0.getReg 2#5).toNat ≤ 0x1400000) (hsp16 : (s0.getReg 2#5).toNat % 16 = 0)
    (hra : (s0.getReg 1#5).toNat % 4 = 0) :
    ∃ m T, run m E = some T ∧ McFinal s0 F len (readWords E.mem MERKLE 8) root rest T := by
  obtain ⟨h2, h26, r0, r1, r2, r3, r4, r5, r6, r7, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27,
    hmE, -⟩ := fr
  have hL : Code.merkle_check.length = 111 := by decide +kernel
  simp only [ROM_END] at hrom hsp0
  have hromL : A.toNat + 4 * Code.merkle_check.length ≤ ROM_END := by rw [hL]; simp only [ROM_END]; omega
  have h2s : E.getReg 2#5 + 96#32 = s0.getReg 2#5 := by rw [h2]; bv_omega
  have hEn : (E.getReg 2#5).toNat + 96 = (s0.getReg 2#5).toNat := by rw [← h2s]; bv_omega
  have h26n : (E.getReg 26#5).toNat = 0x1401000 := by rw [h26]; rfl
  -- block 1: the comparison, words 68 … 93
  obtain ⟨S6, hrun6, hpc6, hin6, hrel6, hrom6, hout6, hfr6⟩ := block_at Code.merkle_check 68 26 MCmp.instrs
    MCmp.σ E A [⟨2, 0, 96, 4⟩, ⟨26, 256, 288, 4⟩] [] MCmp.dec MCmp.run (by decide +kernel) (by rw [hpc])
    hal hromL hcode (by sym_side) (by simp) (by decide +kernel)
  have hsp6 : S6.getReg 2#5 = E.getReg 2#5 :=
    Rel.reg_same MCmp.instrs MCmp.run hrel6 2#5 (by decide +kernel)
  have hz : S6.getReg 10#5 = 0#32 ↔ readWords E.mem MERKLE 8 = root := by
    rw [(hrel6.2.2.1 10#5).2, show (MCmp.σ.reg 10#5).val = 54 from by decide +kernel, exit_cmp,
      exit_mroot E root h26 r0 r1 r2 r3 r4 r5 r6 r7]
    exact Iff.rfl
  -- the frame: memory outside `[sp + 12, sp + 16)` is not touched by the block's store
  have hmemS6 : ∀ a : Word, a.toNat < (E.getReg 2#5).toNat + 12 ∨ (E.getReg 2#5).toNat + 16 ≤ a.toNat →
      S6.mem a = E.mem a := fun a ha =>
    out_frame hfr6 ⟨2, 12, 16, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; omega)
  by_cases hnr : readWords E.mem MERKLE 8 = root
  · -- equal: the branch falls through; the epilogue, `ret`
    have hz0 : S6.getReg 10#5 = 0#32 := hz.mpr hnr
    have hbf : run 1 S6 = some S6.nextInstr :=
      run_branch_f hcode hal hromL hrom6 94 0x04051063#32 (by decide +kernel) (by rw [hpc6])
        Cond.ne 10#5 0#5 0x40#32 (by decide +kernel) (by rw [r_zero5, hz0]; rfl)
    have hpc7 : S6.nextInstr.pc = A + BitVec.ofNat 32 (4 * 95) := by rw [next_pc, hpc6]; bv_omega
    have hmem7 : ∀ b : Word, b.toNat < ROM_END → S6.nextInstr.mem b = E.mem b := fun b hb => by
      rw [next_mem]; exact hrom6 b hb
    have hcode7 : CodeAt S6.nextInstr A Code.merkle_check := codeAt_of_rom hcode hromL hmem7
    have hsp7 : S6.nextInstr.getReg 2#5 = E.getReg 2#5 := by rw [next_r]; exact hsp6
    have hsp7n : (S6.nextInstr.getReg 2#5).toNat = (E.getReg 2#5).toNat := by rw [hsp7]
    obtain ⟨S8, hrun8, hpc8, hin8, hrel8, hrom8, hout8, hfr8⟩ := block_at Code.merkle_check 95 14 MEpi.instrs
      MEpi.σ S6.nextInstr A [⟨2, 0, 96, 4⟩] [] MEpi.dec MEpi.run (by decide +kernel) hpc7 hal hromL hcode7
      (by sym_side) (by simp) (by decide +kernel)
    have hRomE8 : ∀ b : Word, b.toNat < ROM_END → S8.mem b = E.mem b := fun b hb => (hrom8 b hb).trans (hmem7 b hb)
    have hr1 : S8.getReg 1#5 = s0.getReg 1#5 :=
      exit_restore S6.nextInstr S8 E s0 1#5 92#32 4294967292#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => (by rw [next_mem]; exact hmemS6 a (by omega))) (Rel.reg_load MEpi.instrs MEpi.run hrel8 1#5 2 92#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v1
    have hr8 : S8.getReg 8#5 = s0.getReg 8#5 :=
      exit_restore S6.nextInstr S8 E s0 8#5 88#32 4294967288#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 8#5 2 88#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v8
    have hr9 : S8.getReg 9#5 = s0.getReg 9#5 :=
      exit_restore S6.nextInstr S8 E s0 9#5 84#32 4294967284#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 9#5 2 84#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v9
    have hr18 : S8.getReg 18#5 = s0.getReg 18#5 :=
      exit_restore S6.nextInstr S8 E s0 18#5 80#32 4294967280#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 18#5 2 80#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v18
    have hr19 : S8.getReg 19#5 = s0.getReg 19#5 :=
      exit_restore S6.nextInstr S8 E s0 19#5 76#32 4294967276#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 19#5 2 76#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v19
    have hr20 : S8.getReg 20#5 = s0.getReg 20#5 :=
      exit_restore S6.nextInstr S8 E s0 20#5 72#32 4294967272#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 20#5 2 72#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v20
    have hr21 : S8.getReg 21#5 = s0.getReg 21#5 :=
      exit_restore S6.nextInstr S8 E s0 21#5 68#32 4294967268#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 21#5 2 68#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v21
    have hr22 : S8.getReg 22#5 = s0.getReg 22#5 :=
      exit_restore S6.nextInstr S8 E s0 22#5 64#32 4294967264#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 22#5 2 64#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v22
    have hr23 : S8.getReg 23#5 = s0.getReg 23#5 :=
      exit_restore S6.nextInstr S8 E s0 23#5 60#32 4294967260#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 23#5 2 60#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v23
    have hr24 : S8.getReg 24#5 = s0.getReg 24#5 :=
      exit_restore S6.nextInstr S8 E s0 24#5 56#32 4294967256#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 24#5 2 56#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v24
    have hr25 : S8.getReg 25#5 = s0.getReg 25#5 :=
      exit_restore S6.nextInstr S8 E s0 25#5 52#32 4294967252#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 25#5 2 52#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v25
    have hr26 : S8.getReg 26#5 = s0.getReg 26#5 :=
      exit_restore S6.nextInstr S8 E s0 26#5 48#32 4294967248#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 26#5 2 48#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v26
    have hr27 : S8.getReg 27#5 = s0.getReg 27#5 :=
      exit_restore S6.nextInstr S8 E s0 27#5 44#32 4294967244#32 (by decide) (by decide) (by omega) hsp7
        (fun a h1 h2' => by rw [next_mem]; exact hmemS6 a (by omega))
        (Rel.reg_load MEpi.instrs MEpi.run hrel8 27#5 2 44#32 (by decide) (by decide +kernel) (by decide +kernel))
        (by rw [← h2s]; bv_omega) v27
    have hr2 : S8.getReg 2#5 = s0.getReg 2#5 := by
      rw [Rel.reg_addr MEpi.instrs MEpi.run hrel8 2#5 2 96#32 (by decide) (by decide +kernel) (by decide +kernel),
        hsp7, h2s]
    have hcs : ∀ i, calleeSaved i → S8.getReg i = s0.getReg i :=
      calleeSaved_all (fun r => S8.getReg r = s0.getReg r) hr2 hr8 hr9 hr18 hr19 hr20 hr21 hr22 hr23 hr24 hr25 hr26
        hr27
    have hret : run 1 S8 = some S8.ret :=
      run_ret hcode hal hromL hRomE8 109 (by decide +kernel) (by rw [hpc8]) (by rw [hr1]; exact hra)
    refine ⟨26 + 1 + 14 + 1, S8.ret, run_trans (run_trans (run_trans hrun6 hbf) hrun8) hret,
      fun _ => ⟨by rw [ret_pc, hr1], fun i hi => by rw [ret_getReg]; exact hcs i hi,
        by rw [ret_input, hin8, nextInstr_input, hin6, hin],
        fun a ha1 ha2 => by
          rw [ret_mem, Rel.mem_nil hrel8 (by decide +kernel), next_mem, hmemS6 a (by omega)]
          exact hmE a ha1 ha2⟩,
      fun h => absurd hnr h⟩
  · -- differ: the branch is taken, `jal` to `zksync_os_finish_error`, which gets stuck
    have hz1 : S6.getReg 10#5 ≠ 0#32 := fun h => hnr (hz.mp h)
    have hbt : run 1 S6 = some (S6.setPC (A + BitVec.ofNat 32 (4 * 110))) :=
      run_branch_t hcode hal hromL hrom6 94 0x04051063#32 (by decide +kernel) (by rw [hpc6]) RV.Cond.ne 10#5 0#5
        0x40#32 (by decide +kernel) (by rw [r_zero5]; simp [Cond.holds, hz1]) 110 (by decide)
    have hjal : run 1 (S6.setPC (A + BitVec.ofNat 32 (4 * 110))) =
        some (((S6.setPC (A + BitVec.ofNat 32 (4 * 110))).setPC (A + 0x3d4#32)).setReg 1#5
          (A + BitVec.ofNat 32 (4 * 110 + 4))) :=
      run_jal (T := S6.setPC (A + BitVec.ofNat 32 (4 * 110))) hcode hal hromL (fun b hb => hrom6 b hb) 110 0x21c000ef#32 (by decide +kernel) rfl 0x21c#32
        (by decide +kernel) (A + 0x3d4#32) (by bv_omega) (by bv_omega)
    have hjs := run_trans (run_trans hrun6 hbt) hjal
    set S' := ((S6.setPC (A + BitVec.ofNat 32 (4 * 110))).setPC (A + 0x3d4#32)).setReg 1#5
      (A + BitVec.ofNat 32 (4 * 110 + 4)) with hS'
    have hs' : S'.getReg 2#5 = E.getReg 2#5 := by rw [hS', jal_getReg _ _ _ _ (by decide), jump_r, hsp6]
    have hAe : (A + 0x3d4#32).toNat = A.toNat + 980 := by bv_omega
    have herr' : CodeAt S' (A + 0x3d4#32) Code.finish_error :=
      codeAt_of_rom herr (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END] at *; omega)
        (fun b hb => hrom6 b hb)
    obtain ⟨n, T, hT, hst⟩ := finish_error_stuck S' (A + 0x3d4#32) rfl (by bv_omega)
      (by rw [hAe]; simp only [ROM_END] at *; omega) herr' (by rw [hs']; simp only [ROM_END] at *; omega)
      (by rw [hs']; simp only [RAM_END] at *; omega) (by rw [hs']; omega)
    exact ⟨26 + 1 + 1 + n, T, run_trans hjs hT, fun h => absurd h hnr, fun _ => hst⟩
end RV
