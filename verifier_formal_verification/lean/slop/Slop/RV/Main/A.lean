import Slop.RV.Init
import Slop.RV.Combine
import Slop.RV.Poly
import Slop.RV.Coeffs
import Slop.RV.Coeffs4
import Slop.RV.Main.Blocks
import Slop.RV.Input

/-! `main`, first part (both images): the prologue and `init` (`main_init`), the five input reads (`main_reads`),
`u32_combine` and `m31_poly_eval` (`main_a`); up to `main + 0x68`. Blocks by the symbolic executor, calls by their
contracts. -/

namespace RV
open _root_.RV.Sym
set_option maxHeartbeats 0

/-- What `init` does (`init_run`), for an image's `init` at `A` copying `.rodata` from ROM `src`. -/
def InitOK (A src : Word) (codeI : List Word) : Prop :=
  ∀ S : State, CodeAt S A codeI → CodeAt S (A + 136#32) Code.memcpy → S.pc = A →
    (S.getReg 2#5).toNat % 16 = 0 → 4194304 + 32 ≤ (S.getReg 2#5).toNat → (S.getReg 2#5).toNat ≤ 20971520 →
    (S.getReg 1#5).toNat % 4 = 0 →
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      (∀ a : Word, a.toNat + 32 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S'.mem a = blockCopy S.mem 20971520#32 src 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ i : Reg, i ≠ 10#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i)

theorem run_trans {a b : Nat} {S S1 S2 : State} (h1 : run a S = some S1) (h2 : run b S1 = some S2) :
    run (a + b) S = some S2 := by
  rw [run_add, h1, Option.bind_some, h2]

/-- The state after a call instruction: registers other than `ra` as before. -/
theorem jal_getReg (T : State) (t v : Word) (r : Reg) (hr : r ≠ 1#5) :
    ((T.setPC t).setReg 1#5 v).getReg r = T.getReg r := by
  rw [r_set, jump_r]; simp only [hr, ite_false]
  split
  · next h => subst h; rfl
  · rfl

theorem jal_getReg1 (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).getReg 1#5 = v := by
  rw [r_set]; rfl

theorem jal_mem (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).mem = T.mem := by
  rw [set_mem, jump_mem]

theorem jal_pc (T : State) (t v : Word) : ((T.setPC t).setReg 1#5 v).pc = t := rfl

namespace MainA
abbrev rF : Region := ⟨2, -96, 0, 16⟩
end MainA
open MainA

/-- The prologue and `init`: from `main` to the first input read (`main + 0x34`). -/
theorem main_init (S : State) (codeM codeI : List Word) (Ai src : Word)
    (hI : InitOK Ai src codeI) (hIl : codeI.length = 34) (hAi : Ai.toNat % 4 = 0)
    (hAir : Ai.toNat + 136 + 4 * 1676 ≤ 4194304) (hsrc : src.toNat + 912 ≤ 4194304)
    (hpc : S.pc = 0x38#32) (h2 : S.getReg 2#5 = 0x13ffff0#32) (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hmain : CodeAt S 0x38#32 codeM) (hlen : codeM.length = 85) (hb0 : codeM.take 12 = Code.main.take 12)
    (j0 : Word) (hj0 : codeM[12]? = some j0) (dj0 : decode j0 = some (.jal 1#5 (Ai - 0x68#32)))
    (hinit : CodeAt S Ai codeI) (hmc : CodeAt S (Ai + 136#32) Code.memcpy) :
    ∃ m S2, run m S = some S2 ∧ S2.pc = 0x6c#32 ∧ S2.getReg 2#5 = 0x13fff90#32 ∧
      (∀ a : Word, 0x13ffff0 ≤ a.toNat → S2.mem a = blockCopy S.mem 20971520#32 src 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S2.mem b = S.mem b) := by
  have h2n : (S.getReg 2#5).toNat = 0x13ffff0 := by rw [h2]; rfl
  have hl : Code.main.length = 85 := by decide +kernel
  obtain ⟨_, e12⟩ := List.getElem?_eq_some_iff.mp hj0
  simp only [ROM_END, RAM_END] at *
  ------------------------------------------------------------------ prologue, `init`
  have hc0 : CodeAt S 0x38#32 (Code.main.take 12) := hb0 ▸ codeAt_take hmain 12
  obtain ⟨T0, hrun0, hrel0, hrom0, -, hfr0⟩ := block_jal _ Main0.instrs Main0.σ S 0x38#32 (Ai - 0x68#32) [rF] []
    Main0.dec Main0.run hpc (by decide) (by simp [hl, ROM_END]) hc0 j0
    ((hmain 12 (by omega)).trans e12) dj0 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, hl, show min 12 85 = 12 from rfl] at hrun0
  set S1 := (T0.setPC (0x38#32 + BitVec.ofNat 32 (4 * 12) + (Ai - 0x68#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 12) + 4) with hS1
  have s1sp : S1.getReg 2#5 = 0x13fff90#32 := by
    rw [hS1, jal_getReg _ _ _ _ (by decide),
      hrel0.reg_addr _ Main0.run 2#5 2 4294967200#32 (by decide) (by decide +kernel) (by decide +kernel)]
    simp only [show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  have s1rom : ∀ b : Word, b.toNat < 4194304 → S1.mem b = S.mem b := fun b hb => by
    rw [hS1, jal_mem]; exact hrom0 b (by simp only [ROM_END]; omega)
  -- the frame of `main` is all block 0 writes
  have s1mem : ∀ a : Word, a.toNat < 0x13fff90 ∨ 0x13ffff0 ≤ a.toNat → S1.mem a = S.mem a := fun a ha => by
    rw [hS1, jal_mem]
    apply hfr0 [⟨2, -96, 0, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl]; omega
  have s1reg : ∀ r : Reg, (Main0.σ.reg r).val = r.toNat → r ≠ 1#5 → S1.getReg r = S.getReg r := fun r hv hr => by
    rw [hS1, jal_getReg _ _ _ _ hr]; exact hrel0.reg_same _ Main0.run r hv
  obtain ⟨n1, S2, hrun1, hpc2, hmem2, hrom2, hreg2⟩ := hI S1
    (codeAt_of_rom hinit (by rw [hIl]; simp only [ROM_END]; omega) s1rom)
    (codeAt_of_rom hmc (by rw [memcpy_length]; simp only [ROM_END]; bv_omega) s1rom)
    (by rw [hS1, jal_pc]; bv_omega) (by rw [s1sp]; decide) (by rw [s1sp]; decide) (by rw [s1sp]; decide)
    (by rw [hS1, jal_getReg1]; decide)
  rw [hS1, jal_getReg1] at hpc2
  rw [s1sp] at hmem2
  have s2rom : ∀ b : Word, b.toNat < 4194304 → S2.mem b = S.mem b := fun b hb => (hrom2 b (by simp only [ROM_END]; omega)).trans (s1rom b hb)
  -- RAM above `main`'s frame: the `.rodata` copy, else as at the start
  have s2hi : ∀ a : Word, 0x13ffff0 ≤ a.toNat → S2.mem a = blockCopy S.mem 20971520#32 src 912 a := fun a ha => by
    rw [hmem2 a (by right; bv_omega)]
    simp only [blockCopy]; split
    · next h => rw [s1rom _ (by bv_omega)]
    · rw [s1mem a (by right; omega)]
  have s2sp : S2.getReg 2#5 = 0x13fff90#32 := (hreg2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans s1sp
  exact ⟨_, S2, run_trans hrun0 hrun1, by rw [hpc2]; rfl, s2sp, s2hi, s2rom⟩

/-- The five input reads (`csrrw s3/s5/s6/s7/s8, 0x7c0, x0`), from `main + 0x34`. -/
theorem main_reads (R : State) (codeM : List Word) (x y0 y1 y2 y3 : Word) (rest : List Word)
    (hpc : R.pc = 0x6c#32) (hmain : CodeAt R 0x38#32 codeM) (hlen : codeM.length = 85)
    (hb : (codeM.drop 13).take 5 = (Code.main.drop 13).take 5)
    (hin : R.input = x :: y0 :: y1 :: y2 :: y3 :: rest) :
    ∃ R', run 5 R = some R' ∧ R'.pc = 0x80#32 ∧ R'.mem = R.mem ∧ R'.input = rest ∧
      R'.getReg 19#5 = x ∧ R'.getReg 21#5 = y0 ∧ R'.getReg 22#5 = y1 ∧ R'.getReg 23#5 = y2 ∧ R'.getReg 24#5 = y3 ∧
      (∀ r : Reg, r ≠ 19#5 → r ≠ 21#5 → r ≠ 22#5 → r ≠ 23#5 → r ≠ 24#5 → R'.getReg r = R.getReg r) := by
  have hc : CodeAt R (0x38#32 + BitVec.ofNat 32 (4 * 13)) ((Code.main.drop 13).take 5) :=
    hb ▸ codeAt_take (codeAt_drop hmain 13 (by rw [hlen]; bv_omega)) 5
  rw [show (Code.main.drop 13).take 5 = [0x7c0019f3#32, 0x7c001af3#32, 0x7c001b73#32, 0x7c001bf3#32, 0x7c001c73#32]
    by decide +kernel] at hc
  have w : ∀ k (h : k < 5), read R.mem (0x6c#32 + BitVec.ofNat 32 (4 * k)) 4 =
      [0x7c0019f3#32, 0x7c001af3#32, 0x7c001b73#32, 0x7c001bf3#32, 0x7c001c73#32][k] := fun k h => by
    rw [← hc k (by simpa using h)]; congr 1
  set R1 := (R.setReg 19#5 x).nextInstr.withInput (y0 :: y1 :: y2 :: y3 :: rest) with hR1
  set R2 := (R1.setReg 21#5 y0).nextInstr.withInput (y1 :: y2 :: y3 :: rest) with hR2
  set R3 := (R2.setReg 22#5 y1).nextInstr.withInput (y2 :: y3 :: rest) with hR3
  set R4 := (R3.setReg 23#5 y2).nextInstr.withInput (y3 :: rest) with hR4
  set R5 := (R4.setReg 24#5 y3).nextInstr.withInput rest with hR5
  have p1 : R1.pc = 0x70#32 := by rw [hR1]; simp [hpc]
  have p2 : R2.pc = 0x74#32 := by rw [hR2]; simp [p1]
  have p3 : R3.pc = 0x78#32 := by rw [hR3]; simp [p2]
  have p4 : R4.pc = 0x7c#32 := by rw [hR4]; simp [p3]
  have p5 : R5.pc = 0x80#32 := by rw [hR5]; simp [p4]
  have m1 : R1.mem = R.mem := by rw [hR1]; simp
  have m2 : R2.mem = R.mem := by rw [hR2]; simp [m1]
  have m3 : R3.mem = R.mem := by rw [hR3]; simp [m2]
  have m4 : R4.mem = R.mem := by rw [hR4]; simp [m3]
  have m5 : R5.mem = R.mem := by rw [hR5]; simp [m4]
  have s1 := step_read R 0x7c0019f3#32 .rw 19#5 x _ (by rw [hpc]; decide) (by rw [hpc]; decide)
    (by rw [hpc]; exact w 0 (by decide)) (by decide +kernel) hin
  have s2 := step_read R1 0x7c001af3#32 .rw 21#5 y0 _ (by rw [p1]; decide) (by rw [p1]; decide)
    (by rw [p1, m1]; exact w 1 (by decide)) (by decide +kernel) rfl
  have s3 := step_read R2 0x7c001b73#32 .rw 22#5 y1 _ (by rw [p2]; decide) (by rw [p2]; decide)
    (by rw [p2, m2]; exact w 2 (by decide)) (by decide +kernel) rfl
  have s4 := step_read R3 0x7c001bf3#32 .rw 23#5 y2 _ (by rw [p3]; decide) (by rw [p3]; decide)
    (by rw [p3, m3]; exact w 3 (by decide)) (by decide +kernel) rfl
  have s5 := step_read R4 0x7c001c73#32 .rw 24#5 y3 _ (by rw [p4]; decide) (by rw [p4]; decide)
    (by rw [p4, m4]; exact w 4 (by decide)) (by decide +kernel) rfl
  refine ⟨R5, by rw [run_succ, s1, Option.bind_some, ← hR1, run_succ, s2, Option.bind_some, ← hR2, run_succ, s3,
    Option.bind_some, ← hR3, run_succ, s4, Option.bind_some, ← hR4, run_succ, s5, Option.bind_some, ← hR5]; rfl, p5, m5, by rw [hR5, withInput_input], ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hR5, hR4, hR3, hR2, hR1, withInput_getReg, next_r, r_set, BitVec.reduceEq, ite_true,
    ite_false]
  intro r a b c d e
  simp only [a, b, c, d, e, ite_false]
  split <;> simp_all [r_zero5]

namespace MainA2
abbrev rF : Region := ⟨2, -96, 0, 16⟩
end MainA2

/-- `u32_combine` and `m31_poly_eval`: from `main + 0x48` (after the reads) to `main + 0x68`. -/
theorem main_a (S R : State) (codeM : List Word) (Ac Ap src : Word) (x : Word)
    (hAc : Ac.toNat + 0x6c + 36 ≤ 4194304) (hAc4 : Ac.toNat % 4 = 0)
    (hAp : 256 ≤ Ap.toNat) (hAp4 : Ap.toNat % 4 = 0) (hApr : Ap.toNat + 4 * Code.poly_eval.length ≤ 4194304)
    (hsrc : src.toNat + 912 ≤ 4194304)
    (hpc : R.pc = 0x80#32) (h2 : R.getReg 2#5 = 0x13fff90#32) (h19 : R.getReg 19#5 = x)
    (hmain : CodeAt R 0x38#32 codeM) (hlen : codeM.length = 85)
    (hb1 : (codeM.drop 18).take 1 = (Code.main.drop 18).take 1)
    (hb2 : (codeM.drop 20).take 5 = (Code.main.drop 20).take 5)
    (j1 j2 : Word) (hj1 : codeM[19]? = some j1) (hj2 : codeM[25]? = some j2)
    (dj1 : decode j1 = some (.jal 1#5 (Ac - 0x84#32))) (dj2 : decode j2 = some (.jal 1#5 (Ap - 0x9c#32)))
    (hcomb : CodeAt R Ac Code.combine) (hinc : CodeAt R (Ac + 0x6c#32) Code.inc)
    (hdbl : CodeAt R (Ac + 0x48#32) Code.double)
    (hpoly : CodeAt R Ap Code.poly_eval) (hmul : CodeAt R (Ap + 4294967236#32) Code.mul_mod)
    (hadd : CodeAt R (Ap + 4294967184#32) Code.add_mod)
    (hcoef : CodeAt S src Code.COEFFS) (hcoef4 : CodeAt S (src + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hcp : ∀ a : Word, 0x13ffff0 ≤ a.toNat → R.mem a = blockCopy S.mem 20971520#32 src 912 a)
    (hxP : x.toNat ≤ P) :
    ∃ m T, run m R = some T ∧ T.pc = 0xa0#32 ∧ T.getReg 2#5 = 0x13fff90#32 ∧ T.getReg 9#5 = 3#32 * x + 1#32 ∧
      (T.getReg 10#5).toNat ≤ P ∧ (T.getReg 10#5).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      (∀ r : Reg, calleeSaved r → r ≠ 9#5 → T.getReg r = R.getReg r) ∧
      CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ a : Word, 0x13fff90 ≤ a.toNat → T.mem a = R.mem a) ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = R.mem b) := by
  have hl : Code.main.length = 85 := by decide +kernel
  obtain ⟨_, e19⟩ := List.getElem?_eq_some_iff.mp hj1
  obtain ⟨_, e25⟩ := List.getElem?_eq_some_iff.mp hj2
  simp only [ROM_END, RAM_END] at *
  ------------------------------------------------------------------ `combine`
  have hc1 : CodeAt R (0x38#32 + BitVec.ofNat 32 (4 * 18)) ((Code.main.drop 18).take 1) :=
    hb1 ▸ codeAt_take (codeAt_drop hmain 18 (by rw [hlen]; bv_omega)) 1
  obtain ⟨T1, hrunb1, hrel1, hrom1, -, hfr1⟩ := block_jal _ Main1.instrs Main1.σ R _ (Ac - 0x84#32) [] []
    Main1.dec Main1.run (by rw [hpc]; rfl) (by decide) (by simp [hl, ROM_END]) hc1 j1
    (by
      rw [show ((Code.main.drop 18).take 1).length = 1 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 18) + BitVec.ofNat 32 (4 * 1) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 19) by decide]
      exact (hmain 19 (by omega)).trans e19)
    dj1 (by simp; bv_omega) (by simp) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 1 (85 - 18) = 1 from rfl] at hrunb1
  set S3 := (T1.setPC (0x38#32 + BitVec.ofNat 32 (4 * 18) + BitVec.ofNat 32 (4 * 1) + (Ac - 0x84#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 18) + BitVec.ofNat 32 (4 * 1) + 4) with hS3
  have j3 : ∀ r : Reg, r ≠ 1#5 → S3.getReg r = T1.getReg r := fun r hr => by rw [hS3, jal_getReg _ _ _ _ hr]
  have s3x : S3.getReg 10#5 = x := by
    rw [j3 _ (by decide), hrel1.reg_var _ Main1.run 10#5 19 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, h19]
  have s3sp : S3.getReg 2#5 = 0x13fff90#32 := by
    rw [j3 _ (by decide), hrel1.reg_same _ Main1.run _ (by decide +kernel), h2]
  have s3eq : S3.mem = R.mem := by
    rw [hS3, jal_mem]; funext a
    exact hfr1 [] (by decide +kernel) (by simp) a (by simp)
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = R.mem b := fun b _ => by rw [s3eq]
  have hpc3 : S3.pc = Ac := by rw [hS3, jal_pc]; bv_omega
  obtain ⟨n2, S4, hrun2, hpc4, hpost4, hcs4, hmem4⟩ := combine_impl Ac hAc S3 hpc3
    (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h <;> subst h
      · exact codeAt_of_rom hinc (by simp only [Code.inc, List.length_cons, List.length_nil, ROM_END]; bv_omega) s3rom
      · exact codeAt_of_rom hdbl (by simp only [Code.double, List.length_cons, List.length_nil, ROM_END]; bv_omega)
          s3rom)
    ⟨(by
        rw [hpc3]
        exact codeAt_of_rom hcomb (by simp only [Code.combine, List.length_cons, List.length_nil, ROM_END]; bv_omega)
          s3rom),
      (by rw [hpc3]; bv_omega),
      (by rw [hpc3]; simp only [Code.combine, List.length_cons, List.length_nil, ROM_END]; bv_omega),
      (by show (S3.getReg 1#5).toNat % 4 = 0; rw [hS3, jal_getReg1]; decide),
      (by show (S3.getReg 2#5).toNat % 16 = 0; rw [s3sp]; decide),
      (by show ROM_END + 32 ≤ (S3.getReg 2#5).toNat; rw [s3sp]; decide),
      (by show (S3.getReg 2#5).toNat ≤ RAM_END; rw [s3sp]; decide)⟩
  replace hpc4 : S4.pc = S3.getReg 1#5 := hpc4
  replace hcs4 : ∀ i, calleeSaved i → S4.getReg i = S3.getReg i := hcs4
  replace hmem4 : ∀ a : Word, a.toNat + 32 < (S3.getReg 2#5).toNat ∨ (S3.getReg 2#5).toNat ≤ a.toNat →
      S4.mem a = S3.mem a := hmem4
  replace hpost4 : S4.getReg 10#5 = 3 * S3.getReg 10#5 + 1 := hpost4
  rw [s3sp] at hmem4
  rw [hS3, jal_getReg1] at hpc4
  have s4hi : ∀ a : Word, 0x13fff90 ≤ a.toNat → S4.mem a = R.mem a := fun a ha => by
    rw [hmem4 a (by right; bv_omega), s3eq]
  have s4rom : ∀ b : Word, b.toNat < 4194304 → S4.mem b = R.mem b := fun b hb => by
    rw [hmem4 b (by left; simp; omega), s3rom b hb]
  have s4cs : ∀ r : Reg, calleeSaved r → (Main1.σ.reg r).val = r.toNat → S4.getReg r = R.getReg r := fun r h hv => by
    rw [hcs4 r h, j3 r (by rintro rfl; simp [calleeSaved] at h), hrel1.reg_same _ Main1.run r hv]
  have s4sp : S4.getReg 2#5 = 0x13fff90#32 := (hcs4 _ (by rv_callee_saved)).trans s3sp
  ------------------------------------------------------------------ `poly_eval`
  have hc2 : CodeAt S4 (0x38#32 + BitVec.ofNat 32 (4 * 20)) ((Code.main.drop 20).take 5) :=
    codeAt_of_rom (hb2 ▸ codeAt_take (codeAt_drop hmain 20 (by rw [hlen]; bv_omega)) 5)
      (by simp [hl, ROM_END]) s4rom
  obtain ⟨T2, hrunb2, hrel2, hrom2, -, hfr2⟩ := block_jal _ Main2.instrs Main2.σ S4 _ (Ap - 0x9c#32) [] []
    Main2.dec Main2.run (by rw [hpc4]; decide) (by decide) (by simp [hl, ROM_END]) hc2 j2
    (by
      rw [show ((Code.main.drop 20).take 5).length = 5 by decide +kernel,
        read_congr S4.mem R.mem _ 4 (fun j hj => s4rom _ (by bv_omega)),
        show (0x38#32 + BitVec.ofNat 32 (4 * 20) + BitVec.ofNat 32 (4 * 5) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 25) by decide]
      exact (hmain 25 (by omega)).trans e25)
    dj2 (by simp; bv_omega) (by simp) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 5 (85 - 20) = 5 from rfl] at hrunb2
  set S5 := (T2.setPC (0x38#32 + BitVec.ofNat 32 (4 * 20) + BitVec.ofNat 32 (4 * 5) + (Ap - 0x9c#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 20) + BitVec.ofNat 32 (4 * 5) + 4) with hS5
  have j5 : ∀ r : Reg, r ≠ 1#5 → S5.getReg r = T2.getReg r := fun r hr => by rw [hS5, jal_getReg _ _ _ _ hr]
  have s5eq : S5.mem = S4.mem := by
    rw [hS5, jal_mem]; funext a
    exact hfr2 [] (by decide +kernel) (by simp) a (by simp)
  have s5rom : ∀ b : Word, b.toNat < 4194304 → S5.mem b = R.mem b := fun b hb => by rw [s5eq, s4rom b hb]
  have s5sp : S5.getReg 2#5 = 0x13fff90#32 := by
    rw [j5 _ (by decide), hrel2.reg_same _ Main2.run _ (by decide +kernel), s4sp]
  have s5x : S5.getReg 12#5 = x := by
    rw [j5 _ (by decide), hrel2.reg_var _ Main2.run _ 19 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, s4cs _ (by rv_callee_saved) (by decide +kernel), h19]
  have hpc5 : S5.pc = Ap := by rw [hS5, jal_pc]; bv_omega
  -- the `.rodata` copy, seen from `S5`
  have s5copy : ∀ a : Word, (a - 20971520#32).toNat < 912 → S5.mem a = blockCopy S.mem 20971520#32 src 912 a :=
    fun a ha => by rw [s5eq, s4hi a (by bv_omega), hcp a (by bv_omega)]
  obtain ⟨n3, S6, hrun3, hpc6, hpost6, hcs6, hmem6⟩ := poly_eval_impl Ap hAp Code.COEFFS coeffs_le S5 hpc5
    (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h <;> subst h
      · exact codeAt_of_rom hmul (by simp only [Code.mul_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega)
          s5rom
      · exact codeAt_of_rom hadd (by simp only [Code.add_mod, List.length_cons, List.length_nil, ROM_END]; bv_omega)
          s5rom)
    ⟨(by rw [hpc5]; exact codeAt_of_rom hpoly (by simp only [ROM_END]; omega) s5rom),
      (by rw [hpc5]; exact hAp4), (by rw [hpc5]; simp only [ROM_END]; omega),
      (by show (S5.getReg 1#5).toNat % 4 = 0; rw [hS5, jal_getReg1]; decide),
      (by show (S5.getReg 2#5).toNat % 16 = 0; rw [s5sp]; decide),
      (by show ROM_END + 48 ≤ (S5.getReg 2#5).toNat; rw [s5sp]; decide),
      (by show (S5.getReg 2#5).toNat ≤ RAM_END; rw [s5sp]; decide)⟩
    (by
      have a0 : S5.getReg 10#5 = 20971520#32 := by
        rw [j5 _ (by decide), hrel2.reg_cst 10#5 20971520#32 (by decide +kernel)]
      have a1 : S5.getReg 11#5 = 100#32 := by
        rw [j5 _ (by decide), hrel2.reg_cst 11#5 100#32 (by decide +kernel)]
      simp only [polyPre]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show CodeAt S5 (S5.getReg 10#5) Code.COEFFS
        rw [a0]
        exact codeAt_blockCopy_dst hcoef s5copy (by rw [coeffs_length]; decide) (by decide)
      · show S5.getReg 11#5 = BitVec.ofNat 32 Code.COEFFS.length
        rw [a1, coeffs_length]
      · show (S5.getReg 10#5).toNat + 4 * Code.COEFFS.length + 48 ≤ (S5.getReg 2#5).toNat ∨
          (S5.getReg 2#5).toNat ≤ (S5.getReg 10#5).toNat
        rw [a0, s5sp]; right; decide
      · show (S5.getReg 10#5).toNat + 4 * Code.COEFFS.length ≤ 1073741824
        rw [a0, coeffs_length]; decide
      · show (S5.getReg 10#5).toNat % 4 = 0
        rw [a0]; decide
      · show (S5.getReg 12#5).toNat ≤ P
        rw [s5x]; exact hxP)
  replace hpc6 : S6.pc = S5.getReg 1#5 := hpc6
  replace hcs6 : ∀ i, calleeSaved i → S6.getReg i = S5.getReg i := hcs6
  replace hmem6 : ∀ a : Word, a.toNat + 48 < (S5.getReg 2#5).toNat ∨ (S5.getReg 2#5).toNat ≤ a.toNat →
      S6.mem a = S5.mem a := hmem6
  rw [s5sp] at hmem6
  have s5x' : S5.getReg 12 = x := s5x
  simp only [polyPost, s5x'] at hpost6
  refine ⟨_, S6, run_trans (run_trans (run_trans hrunb1 hrun2) hrunb2) hrun3,
    ?_, ?_, ?_, hpost6.1, hpost6.2, ?_, ?_, ?_, ?_⟩
  · rw [hpc6, hS5, jal_getReg1]; decide
  · rw [hcs6 _ (by rv_callee_saved), s5sp]
  · rw [hcs6 _ (by rv_callee_saved), j5 _ (by decide), hrel2.reg_var _ Main2.run _ 10 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 10 : Reg) = 10#5 from rfl, hpost4, s3x]; rfl
  · intro r hr h9
    rw [hcs6 r hr, j5 r (by rintro rfl; simp [calleeSaved] at hr)]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h
    all_goals first
      | exact absurd rfl h9
      | (rw [hrel2.reg_same _ Main2.run _ (by decide +kernel), s4cs _ (by rv_callee_saved) (by decide +kernel)])
  · intro i hi
    rw [read_congr S6.mem S5.mem _ 4 (fun j hj => hmem6 _ (by right; rw [coeffs4_length] at hi; bv_omega))]
    exact codeMem_blockCopy_off hcoef4 s5copy (by rw [coeffs4_length]) (by decide) (by omega) i hi
  · intro a h1
    rw [hmem6 a (by right; bv_omega), s5eq, s4hi a h1]
  · intro b hb
    rw [hmem6 b (by left; bv_omega), s5rom b hb]

end RV
