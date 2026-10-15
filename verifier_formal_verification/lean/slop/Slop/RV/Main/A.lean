import Slop.RV.Init
import Slop.RV.Combine
import Slop.RV.Poly
import Slop.RV.Coeffs
import Slop.RV.Coeffs4
import Slop.RV.Main.Blocks

/-! `main`, first part (both images): the prologue and `init`, the inputs and `u32_combine`, `m31_poly_eval`; up to
`main + 0x70`. Blocks by the symbolic executor, calls by their contracts. -/

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
abbrev rIn : Region := ⟨0, 0x1401000, 0x1401014, 4⟩
end MainA
open MainA

theorem main_a (S : State) (codeM codeI : List Word) (Ai Ac Ap src : Word) (x y0 y1 y2 y3 : Word)
    (hI : InitOK Ai src codeI) (hIl : codeI.length = 34) (hAi : Ai.toNat % 4 = 0) (hAir : Ai.toNat + 136 + 4 * 1676 ≤ 4194304)
    (hAc : Ac.toNat + 0x6c + 36 ≤ 4194304) (hAc4 : Ac.toNat % 4 = 0)
    (hAp : 256 ≤ Ap.toNat) (hAp4 : Ap.toNat % 4 = 0) (hApr : Ap.toNat + 4 * Code.poly_eval.length ≤ 4194304)
    (hsrc : src.toNat + 912 ≤ 4194304)
    (hpc : S.pc = 0x38#32) (h2 : S.getReg 2#5 = 0x13ffff0#32) (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hmain : CodeAt S 0x38#32 codeM) (hlen : codeM.length = 85)
    (hb0 : codeM.take 12 = Code.main.take 12) (hb1 : (codeM.drop 13).take 8 = (Code.main.drop 13).take 8)
    (hb2 : (codeM.drop 22).take 5 = (Code.main.drop 22).take 5)
    (j0 j1 j2 : Word) (hj0 : codeM[12]? = some j0) (hj1 : codeM[21]? = some j1) (hj2 : codeM[27]? = some j2)
    (dj0 : decode j0 = some (.jal 1#5 (Ai - 0x68#32))) (dj1 : decode j1 = some (.jal 1#5 (Ac - 0x8c#32)))
    (dj2 : decode j2 = some (.jal 1#5 (Ap - 0xa4#32)))
    (hinit : CodeAt S Ai codeI) (hmc : CodeAt S (Ai + 136#32) Code.memcpy)
    (hcomb : CodeAt S Ac Code.combine) (hinc : CodeAt S (Ac + 0x6c#32) Code.inc)
    (hdbl : CodeAt S (Ac + 0x48#32) Code.double)
    (hpoly : CodeAt S Ap Code.poly_eval) (hmul : CodeAt S (Ap + 4294967236#32) Code.mul_mod)
    (hadd : CodeAt S (Ap + 4294967184#32) Code.add_mod)
    (hcoef : CodeAt S src Code.COEFFS) (hcoef4 : CodeAt S (src + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hx : read S.mem 0x1401000#32 4 = x) (hy0 : read S.mem 0x1401004#32 4 = y0)
    (hy1 : read S.mem 0x1401008#32 4 = y1) (hy2 : read S.mem 0x140100c#32 4 = y2)
    (hy3 : read S.mem 0x1401010#32 4 = y3) (hxP : x.toNat ≤ P) :
    ∃ m T, run m S = some T ∧ T.pc = 0xa8#32 ∧ T.getReg 2#5 = 0x13fff90#32 ∧ T.getReg 9#5 = 3#32 * x + 1#32 ∧
      (T.getReg 10#5).toNat ≤ P ∧ (T.getReg 10#5).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      T.getReg 19#5 = x ∧ T.getReg 20#5 = 0x1401000#32 ∧ T.getReg 21#5 = y3 ∧ T.getReg 22#5 = y2 ∧
      T.getReg 23#5 = y1 ∧ T.getReg 24#5 = y0 ∧
      CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ a : Word, 0x1400390 ≤ a.toNat → a.toNat < 0x2000000 → T.mem a = S.mem a) ∧
      (∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b) := by
  have h2n : (S.getReg 2#5).toNat = 0x13ffff0 := by rw [h2]; rfl
  have hl : Code.main.length = 85 := by decide +kernel
  obtain ⟨_, e12⟩ := List.getElem?_eq_some_iff.mp hj0
  obtain ⟨_, e21⟩ := List.getElem?_eq_some_iff.mp hj1
  obtain ⟨_, e27⟩ := List.getElem?_eq_some_iff.mp hj2
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
  have s2in : ∀ a : Word, 0x1400390 ≤ a.toNat → S2.mem a = S.mem a := fun a ha => by
    rw [s2hi a (by omega), blockCopy_outside _ _ _ _ _ (by bv_omega)]
  have s2r : ∀ r : Reg, r ≠ 10#5 → r ≠ 11#5 → r ≠ 12#5 → r ≠ 13#5 → r ≠ 14#5 → r ≠ 15#5 →
      (Main0.σ.reg r).val = r.toNat → r ≠ 1#5 → S2.getReg r = S.getReg r := fun r a b c d e f hv h1 =>
    (hreg2 r a b c d e f).trans (s1reg r hv h1)
  have s2sp : S2.getReg 2#5 = 0x13fff90#32 := (hreg2 _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans s1sp
  ------------------------------------------------------------------ the inputs, `combine`
  have hc1 : CodeAt S2 (0x38#32 + BitVec.ofNat 32 (4 * 13)) ((Code.main.drop 13).take 8) :=
    codeAt_of_rom (hb1 ▸ codeAt_take (codeAt_drop hmain 13 (by rw [hlen]; bv_omega)) 8)
      (by simp [hl, ROM_END]) s2rom
  obtain ⟨T1, hrunb1, hrel1, hrom1, -, hfr1⟩ := block_jal _ Main1.instrs Main1.σ S2 _ (Ac - 0x8c#32) [rIn] []
    Main1.dec Main1.run (by rw [hpc2]; rfl) (by decide) (by simp [hl, ROM_END]) hc1 j1
    (by
      rw [show ((Code.main.drop 13).take 8).length = 8 by decide +kernel,
        read_congr S2.mem S.mem _ 4 (fun j hj => s2rom _ (by bv_omega)),
        show (0x38#32 + BitVec.ofNat 32 (4 * 13) + BitVec.ofNat 32 (4 * 8) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 21) by decide]
      exact (hmain 21 (by omega)).trans e21)
    dj1 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 8 (85 - 13) = 8 from rfl] at hrunb1
  set S3 := (T1.setPC (0x38#32 + BitVec.ofNat 32 (4 * 13) + BitVec.ofNat 32 (4 * 8) + (Ac - 0x8c#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 13) + BitVec.ofNat 32 (4 * 8) + 4) with hS3
  have rd : ∀ (k : Word) (v : Word), 0x1401000 ≤ k.toNat → k.toNat + 4 ≤ 0x1401014 → read S.mem k 4 = v →
      read S2.mem (S2.getReg (BitVec.ofNat 5 0) + k) 4 = v := fun k v h1 h2 h => by
    rw [getReg_x0, BitVec.zero_add, ← h]
    exact read_congr _ _ _ _ (fun j hj => s2in _ (by bv_omega))
  have ld : ∀ i (k v : Word), i < Main1.σ.pool.len → nodeAt Main1.σ.pool i = .load 4 true 0 k →
      0x1401000 ≤ k.toNat → k.toNat + 4 ≤ 0x1401014 → read S.mem k 4 = v →
      Main1.σ.pool.val (ctxOf S2) i = v := fun i k v hi h h1 h2 hv => by
    rw [load_val _ _ Main1.run S2 i 0 k true (by decide) hi h]; exact rd k v h1 h2 hv
  have rv1 : ∀ (r : Reg) (i : Nat), (Main1.σ.reg r).val = i → T1.getReg r = Main1.σ.pool.val (ctxOf S2) i :=
    fun r i h => by rw [(hrel1.2.2.1 r).2, h]
  have j3 : ∀ r : Reg, r ≠ 1#5 → S3.getReg r = T1.getReg r := fun r hr => by rw [hS3, jal_getReg _ _ _ _ hr]
  have s3x : S3.getReg 10#5 = x := by
    rw [j3 _ (by decide), rv1 _ 37 (by decide +kernel), ld 37 0x1401000#32 x (by decide +kernel) (by decide +kernel)
      (by decide) (by decide) hx]
  have s3sp : S3.getReg 2#5 = 0x13fff90#32 := by
    rw [j3 _ (by decide), hrel1.reg_same _ Main1.run _ (by decide +kernel), s2sp]
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = S.mem b := fun b hb => by
    rw [hS3, jal_mem, hrom1 b (by simp only [ROM_END]; omega), s2rom b hb]
  have s3eq : S3.mem = S2.mem := by
    rw [hS3, jal_mem]; funext a
    exact hfr1 [] (by decide +kernel) (by simp) a (by simp)
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
  have s4hi : ∀ a : Word, 0x13fff90 ≤ a.toNat → S4.mem a = S2.mem a := fun a ha => by
    rw [hmem4 a (by right; bv_omega), s3eq]
  have s4rom : ∀ b : Word, b.toNat < 4194304 → S4.mem b = S.mem b := fun b hb => by
    rw [hmem4 b (by left; simp; omega), s3rom b hb]
  have s4cs : ∀ r : Reg, calleeSaved r → (Main1.σ.reg r).val = r.toNat → S4.getReg r = S2.getReg r := fun r h hv => by
    rw [hcs4 r h, j3 r (by rintro rfl; simp [calleeSaved] at h), hrel1.reg_same _ Main1.run r hv]
  have s4r : ∀ (r : Reg) (i : Nat), calleeSaved r → (Main1.σ.reg r).val = i →
      S4.getReg r = Main1.σ.pool.val (ctxOf S2) i := fun r i h hv => by
    rw [hcs4 r h, j3 r (by rintro rfl; simp [calleeSaved] at h), rv1 r i hv]
  have s4sp : S4.getReg 2#5 = 0x13fff90#32 := (hcs4 _ (by rv_callee_saved)).trans s3sp
  ------------------------------------------------------------------ `poly_eval`
  have hc2 : CodeAt S4 (0x38#32 + BitVec.ofNat 32 (4 * 22)) ((Code.main.drop 22).take 5) :=
    codeAt_of_rom (hb2 ▸ codeAt_take (codeAt_drop hmain 22 (by rw [hlen]; bv_omega)) 5)
      (by simp [hl, ROM_END]) s4rom
  obtain ⟨T2, hrunb2, hrel2, hrom2, -, hfr2⟩ := block_jal _ Main2.instrs Main2.σ S4 _ (Ap - 0xa4#32) [] []
    Main2.dec Main2.run (by rw [hpc4]; decide) (by decide) (by simp [hl, ROM_END]) hc2 j2
    (by
      rw [show ((Code.main.drop 22).take 5).length = 5 by decide +kernel,
        read_congr S4.mem S.mem _ 4 (fun j hj => s4rom _ (by bv_omega)),
        show (0x38#32 + BitVec.ofNat 32 (4 * 22) + BitVec.ofNat 32 (4 * 5) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 27) by decide]
      exact (hmain 27 (by omega)).trans e27)
    dj2 (by simp; bv_omega) (by simp) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 5 (85 - 22) = 5 from rfl] at hrunb2
  set S5 := (T2.setPC (0x38#32 + BitVec.ofNat 32 (4 * 22) + BitVec.ofNat 32 (4 * 5) + (Ap - 0xa4#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 22) + BitVec.ofNat 32 (4 * 5) + 4) with hS5
  have j5 : ∀ r : Reg, r ≠ 1#5 → S5.getReg r = T2.getReg r := fun r hr => by rw [hS5, jal_getReg _ _ _ _ hr]
  have s5eq : S5.mem = S4.mem := by
    rw [hS5, jal_mem]; funext a
    exact hfr2 [] (by decide +kernel) (by simp) a (by simp)
  have s5rom : ∀ b : Word, b.toNat < 4194304 → S5.mem b = S.mem b := fun b hb => by rw [s5eq, s4rom b hb]
  have s5sp : S5.getReg 2#5 = 0x13fff90#32 := by
    rw [j5 _ (by decide), hrel2.reg_same _ Main2.run _ (by decide +kernel), s4sp]
  have s5x : S5.getReg 12#5 = x := by
    rw [j5 _ (by decide), hrel2.reg_var _ Main2.run _ 19 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 19 : Reg) = 19#5 from rfl, s4r _ 37 (by rv_callee_saved) (by decide +kernel),
      ld 37 0x1401000#32 x (by decide +kernel) (by decide +kernel) (by decide) (by decide) hx]
  have hpc5 : S5.pc = Ap := by rw [hS5, jal_pc]; bv_omega
  -- the `.rodata` copy, seen from `S5`
  have s5copy : ∀ a : Word, (a - 20971520#32).toNat < 912 → S5.mem a = blockCopy S.mem 20971520#32 src 912 a :=
    fun a ha => by rw [s5eq, s4hi a (by bv_omega), s2hi a (by bv_omega)]
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
  have s6r : ∀ (r : Reg), calleeSaved r → (Main2.σ.reg r).val = r.toNat → S6.getReg r = S4.getReg r :=
    fun r h hv => by
      rw [hcs6 r h, j5 r (by rintro rfl; simp [calleeSaved] at h), hrel2.reg_same _ Main2.run r hv]
  have s6y : ∀ (r : Reg) (i : Nat) (k v : Word), calleeSaved r → (Main2.σ.reg r).val = r.toNat →
      (Main1.σ.reg r).val = i → i < Main1.σ.pool.len → nodeAt Main1.σ.pool i = .load 4 true 0 k →
      0x1401000 ≤ k.toNat → k.toNat + 4 ≤ 0x1401014 → read S.mem k 4 = v → S6.getReg r = v :=
    fun r i k v h hv2 hv1 hi hn h1 h2 hv => by rw [s6r r h hv2, s4r r i h hv1, ld i k v hi hn h1 h2 hv]
  refine ⟨_, S6,
    run_trans (run_trans (run_trans (run_trans (run_trans hrun0 hrun1) hrunb1) hrun2) hrunb2) hrun3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 3
  · exact hpost6.1
  · exact hpost6.2
  rotate_right 3
  · rw [hpc6, hS5, jal_getReg1]; decide
  · rw [hcs6 _ (by rv_callee_saved), s5sp]
  · rw [hcs6 _ (by rv_callee_saved), j5 _ (by decide), hrel2.reg_var _ Main2.run _ 10 (by decide) (by decide +kernel),
      show (BitVec.ofNat 5 10 : Reg) = 10#5 from rfl, hpost4, s3x]; rfl
  · exact s6y 19#5 37 0x1401000#32 x (by rv_callee_saved) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) hx
  · rw [s6r _ (by rv_callee_saved) (by decide +kernel), hcs4 _ (by rv_callee_saved), j3 _ (by decide),
      hrel1.reg_cst 20#5 20975616#32 (by decide +kernel)]
  · exact s6y 21#5 33 0x1401010#32 y3 (by rv_callee_saved) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) hy3
  · exact s6y 22#5 34 0x140100c#32 y2 (by rv_callee_saved) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) hy2
  · exact s6y 23#5 35 0x1401008#32 y1 (by rv_callee_saved) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) hy1
  · exact s6y 24#5 36 0x1401004#32 y0 (by rv_callee_saved) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide) (by decide) hy0
  · intro i hi
    rw [read_congr S6.mem S5.mem _ 4 (fun j hj => hmem6 _ (by right; rw [coeffs4_length] at hi; bv_omega))]
    exact codeMem_blockCopy_off hcoef4 s5copy (by rw [coeffs4_length]) (by decide) (by omega) i hi
  · intro a h1 h2
    rw [hmem6 a (by right; bv_omega), s5eq, s4hi a (by omega), s2in a h1]
  · intro b hb
    rw [hmem6 b (by left; bv_omega), s5rom b hb]

end RV
