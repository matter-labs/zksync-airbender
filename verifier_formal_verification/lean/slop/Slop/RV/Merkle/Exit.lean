import Slop.RV.Tactic
import Slop.RV.Input
import Slop.RV.CopyRun
import Slop.RV.Stuck
import Slop.RV.FsCheck.Blocks
import Slop.RV.Code.merkle_check
import Human.SpecMerkle

/-! `merkle_check`, the end (from word 68): the node in `MERKLE.state` against the root (in `s9 … s2`), then either
the epilogue and `ret` (they match) or `zksync_os_finish_error` (they differ: the run gets stuck). -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- `zksync_os_finish_error` (its code at `Aerr`, 16 free bytes below `sp`): the run reaches its
`csrrw x0, cycle, x0`. -/
theorem finish_error_stuck (S : State) (Aerr : Word) (hpc : S.pc = Aerr) (hAerr : Aerr.toNat % 4 = 0)
    (hAerrr : Aerr.toNat + 24 ≤ ROM_END) (herr : CodeAt S Aerr Code.finish_error)
    (hsp1 : ROM_END + 16 ≤ (S.getReg 2#5).toNat) (hsp2 : (S.getReg 2#5).toNat ≤ RAM_END)
    (hsp3 : (S.getReg 2#5).toNat % 16 = 0) :
    ∃ n T, run n S = some T ∧ AtFinishError T := by
  have hLe4 : (Code.finish_error.take 4).length = 4 := by decide +kernel
  have hLe : Code.finish_error.length = 6 := by decide +kernel
  simp only [ROM_END, RAM_END] at *
  obtain ⟨S6, hrun6, hpc6, -, hrom6, -, -⟩ := block_from _ FinErr.instrs FinErr.σ S Aerr [⟨2, -16, 0, 16⟩] []
    FinErr.dec FinErr.run hpc hAerr (by rw [hLe4]; simp only [ROM_END]; omega)
    (codeAt_take herr 4) (by sym_side) (by simp) (by decide +kernel)
  rw [hLe4] at hrun6 hpc6
  refine ⟨4, S6, hrun6, by rw [hpc6]; bv_omega, by rw [hpc6]; simp only [ROM_END]; bv_omega, ?_⟩
  rw [read_congr S6.mem S.mem _ 4 (fun j hj => hrom6 _ (by rw [hpc6]; simp only [ROM_END]; bv_omega)), hpc6]
  exact herr 4 (by rw [hLe]; decide)

/-- `MERKLE`, the evaluator of the path. -/
abbrev MERKLE : Word := 0x1401100#32

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

/-- What `merkle_check` ends with, from its start `s0` (frame `F` bytes), the node it computed and the root it
read: matching, it returns (input left: `rest`); differing, the run is stuck in `zksync_os_finish_error`. -/
def McFinal (s0 : State) (F len : Nat) (node root : Vector Word 8) (rest : List Word) (T : State) : Prop :=
  (node = root → T.pc = s0.getReg 1#5 ∧ (∀ i, calleeSaved i → T.getReg i = s0.getReg i) ∧ T.input = rest ∧
    ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → T.mem a = s0.mem a) ∧
  (node ≠ root → AtFinishError T)

/-- `merkle_check`'s frame (`sp = sp₀ - 96`, `s1 = MERKLE`, `s10 = MERKLE - 0x100`), the registers it saved
there, the root in `s9 … s2` (as read), memory outside the frame and `MERKLE` and ROM as at the start `s0`. -/
structure MFrame (s0 : State) (F len : Nat) (root : Vector Word 8) (E : State) : Prop where
  sp : E.getReg 2#5 = s0.getReg 2#5 + 4294967200#32
  s10 : E.getReg 26#5 = 0x1401000#32
  r0 : E.getReg 25#5 = root[0]
  r1 : E.getReg 24#5 = root[1]
  r2 : E.getReg 23#5 = root[2]
  r3 : E.getReg 22#5 = root[3]
  r4 : E.getReg 20#5 = root[4]
  r5 : E.getReg 21#5 = root[5]
  r6 : E.getReg 19#5 = root[6]
  r7 : E.getReg 18#5 = root[7]
  v1 : read E.mem (s0.getReg 2#5 + 4294967292#32) 4 = s0.getReg 1#5
  v8 : read E.mem (s0.getReg 2#5 + 4294967288#32) 4 = s0.getReg 8#5
  v9 : read E.mem (s0.getReg 2#5 + 4294967284#32) 4 = s0.getReg 9#5
  v18 : read E.mem (s0.getReg 2#5 + 4294967280#32) 4 = s0.getReg 18#5
  v19 : read E.mem (s0.getReg 2#5 + 4294967276#32) 4 = s0.getReg 19#5
  v20 : read E.mem (s0.getReg 2#5 + 4294967272#32) 4 = s0.getReg 20#5
  v21 : read E.mem (s0.getReg 2#5 + 4294967268#32) 4 = s0.getReg 21#5
  v22 : read E.mem (s0.getReg 2#5 + 4294967264#32) 4 = s0.getReg 22#5
  v23 : read E.mem (s0.getReg 2#5 + 4294967260#32) 4 = s0.getReg 23#5
  v24 : read E.mem (s0.getReg 2#5 + 4294967256#32) 4 = s0.getReg 24#5
  v25 : read E.mem (s0.getReg 2#5 + 4294967252#32) 4 = s0.getReg 25#5
  v26 : read E.mem (s0.getReg 2#5 + 4294967248#32) 4 = s0.getReg 26#5
  v27 : read E.mem (s0.getReg 2#5 + 4294967244#32) 4 = s0.getReg 27#5
  mem : ∀ a : Word, a.toNat + F < (s0.getReg 2#5).toNat ∨ (s0.getReg 2#5).toNat ≤ a.toNat →
    a.toNat < MERKLE.toNat ∨ MERKLE.toNat + len ≤ a.toNat → E.mem a = s0.mem a
  rom : ∀ b : Word, b.toNat < ROM_END → E.mem b = s0.mem b

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
  simp only [ROM_END] at *
  rv_code_facts hcode Code.merkle_check
  rv_steps 26 with hpc, h2, h26, r0, r1, r2, r3, r4, r5, r6, r7
  have mw : ∀ i (h : i < 8), read E.mem (20975872#32 + BitVec.ofNat 32 (4 * i)) 4 = (readWords E.mem MERKLE 8)[i] :=
    fun i h => by simp [readWords]
  by_cases hnr : readWords E.mem MERKLE 8 = root
  · have m : ∀ i (h : i < 8), read E.mem (20975872#32 + BitVec.ofNat 32 (4 * i)) 4 = root[i] := fun i h => by
      rw [mw i h, hnr]
    have m0 := m 0 (by decide); have m1 := m 1 (by decide); have m2 := m 2 (by decide); have m3 := m 3 (by decide)
    have m4 := m 4 (by decide); have m5 := m 5 (by decide); have m6 := m 6 (by decide); have m7 := m 7 (by decide)
    simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul] at m0 m1 m2 m3 m4 m5 m6 m7
    rv_steps 1 with hpc, h2, m0, m1, m2, m3, m4, m5, m6, m7, BitVec.xor_self, BitVec.or_self, BitVec.zero_or,
      BitVec.or_zero
    rw [exec_branch_f _ _ _ _ _ ?hb]
    case hb => simp only [rv_state, reduceRSet, Cond.holds, BitVec.reduceEq, ite_true, ite_false]; decide
    rv_steps 15 with hpc, h2, v1, v8, v9, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27
    rv_ret
    refine ⟨fun _ => ⟨by rv_regs, by rv_callee,
      by simp only [setReg_input, nextInstr_input, setPC_input, store_input]; exact hin, fun a ha hb => ?_⟩, fun h => absurd hnr h⟩
    simp only [set_mem, jump_mem, next_mem, store_mem]
    rw [write_outside (h := by bv_omega) (ha := by bv_omega), hmE a ha hb]
  · rv_cut
    have hD : cv_0 ≠ 0#32 := by
      rw [← cvdef_0]
      intro hD
      simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at hD
      apply hnr
      apply Vector.ext; intro i hi
      rw [← mw i hi]
      interval_cases i <;> simp only [BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, BitVec.add_zero] <;>
        exact Eq.symm (by simp only [hD])
    apply run_of_step
    rv_step_simp with hpc
    rv_steps 1 with hpc
    have hsrom : ∀ b : Word, b.toNat < ROM_END → S.mem b = E.mem b := fun b hb => by
      simp only [ROM_END] at hb
      rw [cut_mem, write_outside (h := Or.inl (by bv_omega)) (ha := by bv_omega)]
    obtain ⟨n, T, hT, hst⟩ := finish_error_stuck (((S.setPC (A + 440#32)).setPC (A + 980#32)).setReg (1#5) (A + 444#32)) (A + 0x3d4#32) (by simp only [rv_state, reduceRSet])
      (by bv_omega) (by simp only [ROM_END]; bv_omega)
      (codeAt_of_rom herr (by rw [show Code.finish_error.length = 6 by decide +kernel]; simp only [ROM_END]; bv_omega)
        (fun b hb => by simp only [rv_state]; exact hsrom b hb))
      (by simp only [rv_state, reduceRSet, cut_r2, h2, ROM_END]; bv_omega)
      (by simp only [rv_state, reduceRSet, cut_r2, h2, RAM_END]; bv_omega)
      (by simp only [rv_state, reduceRSet, cut_r2, h2]; bv_omega)
    exact ⟨n, T, hT, fun h => absurd h hnr, fun _ => hst⟩

end RV
