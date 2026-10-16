import Slop.RV.Main.A
import Slop.RV.Ext4Call
import Slop.RV.Blake.Impl

/-! `main`, second part (both images): `ext4_poly` (any implementation of its contract) and `blake2s_compress`;
from `main + 0x68` to `main + 0x114`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

namespace MainB
abbrev rF : Region := ⟨2, 0, 112, 16⟩
abbrev rBl : Region := ⟨0, 0x1401000, 0x1401054, 4⟩
end MainB
open MainB

theorem val_const {p : Pool} (hw : p.WF) (c : Ctx) (i : Nat) (w : Word) (hi : i < p.len)
    (h : nodeAt p i = .const w) : p.val c i = w := by
  rw [(nodeAt_spec c p hw i hi).2, h]; rfl

theorem main_b (T : State) (codeM : List Word) (Aep Ab : Word) (codeEP : List Word)
    (calleesEP : List (Word × List Word)) (FEP : Nat)
    (hEP : ImplementsAtW Aep codeEP calleesEP FEP e4polyPre 16 e4polyPost)
    (hEPr : Aep.toNat + 4 * codeEP.length ≤ 4194304) (hEP4 : Aep.toNat % 4 = 0) (hFEP : FEP ≤ 0x100000)
    (hcalr : ∀ c ∈ calleesEP, c.1.toNat + 4 * c.2.length ≤ 4194304)
    (hAb : Ab.toNat % 4 = 0) (hAbr : Ab.toNat + 4 * Code.blake2s_compress.length ≤ 4194304)
    (c p x y0 y1 y2 y3 : Word)
    (hpc : T.pc = 0xa0#32) (h2 : T.getReg 2#5 = 0x13fff80#32) (h9 : T.getReg 9#5 = c) (h10 : T.getReg 10#5 = p)
    (h20 : T.getReg 20#5 = x) (h21 : T.getReg 21#5 = y0)
    (h22 : T.getReg 22#5 = y1) (h23 : T.getReg 23#5 = y2) (h24 : T.getReg 24#5 = y3)
    (htab : CodeMem T.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4)
    (hz : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401100 → T.mem a = 0)
    (hmain : CodeAt T 0x38#32 codeM) (hlen : codeM.length = 96)
    (hb3 : (codeM.drop 26).take 7 = (Code.main.drop 26).take 7)
    (hb4 : (codeM.drop 34).take 34 = (Code.main.drop 34).take 34)
    (j3 j4 : Word) (hj3 : codeM[33]? = some j3) (hj4 : codeM[68]? = some j4)
    (dj3 : decode j3 = some (.jal 1#5 (Aep - 0xbc#32))) (dj4 : decode j4 = some (.jal 1#5 (Ab - 0x148#32)))
    (hEPc : CodeAt T Aep codeEP) (hcal : ∀ c ∈ calleesEP, CodeAt T c.1 c.2)
    (hbl : CodeAt T Ab Code.blake2s_compress)
    (hy0 : y0.toNat < BabyBearP) (hy1 : y1.toNat < BabyBearP) (hy2 : y2.toNat < BabyBearP)
    (hy3 : y3.toNat < BabyBearP) :
    ∃ m U, run m T = some U ∧ U.pc = 0x14c#32 ∧ U.getReg 2#5 = 0x13fff80#32 ∧ U.getReg 9#5 = c ∧
      U.getReg 18#5 = p ∧ U.getReg 19#5 = 0x1401000#32 ∧
      canon4 U.mem 0x13fff88#32 ∧
      limbsAt U.mem 0x13fff88#32 = poly4 (ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F)) ∧
      wordsAt U.mem 0x1401000#32 8 = blake5 #v[x, y0, y1, y2, y3] ∧
      CodeMem U.mem (0x1400000#32 + BitVec.ofNat 32 0x190) Code.COEFFS4 ∧
      (∀ b : Word, b.toNat < ROM_END → U.mem b = T.mem b) := by
  have hl : Code.main.length = 96 := by decide +kernel
  obtain ⟨_, e33⟩ := List.getElem?_eq_some_iff.mp hj3
  obtain ⟨_, e68⟩ := List.getElem?_eq_some_iff.mp hj4
  have h2n : (T.getReg 2#5).toNat = 0x13fff80 := by rw [h2]; rfl
  simp only [ROM_END, RAM_END] at *
  ------------------------------------------------------------------ `ext4_poly`
  have hc3 : CodeAt T (0x38#32 + BitVec.ofNat 32 (4 * 26)) ((Code.main.drop 26).take 7) :=
    hb3 ▸ codeAt_take (codeAt_drop hmain 26 (by rw [hlen]; bv_omega)) 7
  obtain ⟨T3, hrun3, hrel3, hrom3, hout3, hfr3⟩ := block_jal _ Main3.instrs Main3.σ T _ (Aep - 0xbc#32) [rF] []
    Main3.dec Main3.run (by rw [hpc]; decide) (by decide) (by simp [hl, ROM_END]) hc3 j3
    (by
      rw [show ((Code.main.drop 26).take 7).length = 7 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 33) by decide]
      exact (hmain 33 (by omega)).trans e33)
    dj3 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 7 (96 - 26) = 7 from rfl] at hrun3
  set S1 := (T3.setPC (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) + (Aep - 0xbc#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 26) + BitVec.ofNat 32 (4 * 7) + 4) with hS1
  have j1 : ∀ r : Reg, r ≠ 1#5 → S1.getReg r = T3.getReg r := fun r hr => by rw [hS1, jal_getReg _ _ _ _ hr]
  have hpc1 : S1.pc = Aep := by rw [hS1, jal_pc]; bv_omega
  have s1rom : ∀ b : Word, b.toNat < 4194304 → S1.mem b = T.mem b := fun b hb => by
    rw [hS1, jal_mem]; exact hrom3 b (by simp only [ROM_END]; omega)
  have s1sp : S1.getReg 2#5 = 0x13fff80#32 := by
    rw [j1 _ (by decide), hrel3.reg_same _ Main3.run _ (by decide +kernel), h2]
  have s1a0 : S1.getReg 10#5 = 0x13fff88#32 := by
    rw [j1 _ (by decide), hrel3.reg_addr _ Main3.run 10#5 2 8#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  have s1a1 : S1.getReg 11#5 = 0x13fffa8#32 := by
    rw [j1 _ (by decide), hrel3.reg_addr _ Main3.run 11#5 2 40#32 (by decide) (by decide +kernel) (by decide +kernel),
      show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl, h2]; rfl
  -- the stored `y`, and memory outside `main`'s frame unchanged
  have st : ∀ (k : Word) (i : Nat) (v : Word), outOK Main3.σ [rF] [] 2 k = true → outNode Main3.σ 2 k = i →
      i < 32 → T.getReg (BitVec.ofNat 5 i) = v → read S1.mem (0x13fff80#32 + k) 4 = v := fun k i v h hn hi hv => by
    rw [hS1, jal_mem, ← h2, ← hv, ← val_init _ _ Main3.run T i hi, ← hn]; exact hout3 2 k (by decide) h
  have sy0 := st 40#32 21 y0 (by decide +kernel) (by decide +kernel) (by decide) h21
  have sy1 := st 44#32 22 y1 (by decide +kernel) (by decide +kernel) (by decide) h22
  have sy2 := st 48#32 23 y2 (by decide +kernel) (by decide +kernel) (by decide) h23
  have sy3 := st 52#32 24 y3 (by decide +kernel) (by decide +kernel) (by decide) h24
  simp only [BitVec.reduceAdd] at sy0 sy1 sy2 sy3
  have s1out : ∀ a : Word, (a.toNat < 0x13fff80 ∨ 0x13ffff0 ≤ a.toNat) → S1.mem a = T.mem a := fun a ha => by
    rw [hS1, jal_mem]
    apply hfr3 [⟨2, 0, 112, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, show (BitVec.ofNat 5 2 : Reg) = 2#5 from rfl]; omega
  obtain ⟨n2, S2, hrun2, hpc2, hpost2, hcs2, hmem2⟩ := hEP S1 hpc1
    (fun c hc => codeAt_of_rom (hcal c hc) (by have := hcalr c hc; simp only [ROM_END]; omega) s1rom)
    ⟨(by rw [hpc1]; exact codeAt_of_rom hEPc (by simp only [ROM_END]; omega) s1rom),
      (by rw [hpc1]; exact hEP4), (by rw [hpc1]; simp only [ROM_END]; omega),
      (by show (S1.getReg 1#5).toNat % 4 = 0; rw [hS1, jal_getReg1]; decide),
      (by show (S1.getReg 2#5).toNat % 16 = 0; rw [s1sp]; decide),
      (by show ROM_END + FEP ≤ (S1.getReg 2#5).toNat; rw [s1sp]; simp only [ROM_END]; bv_omega),
      (by show (S1.getReg 2#5).toNat ≤ RAM_END; rw [s1sp]; decide)⟩
    (by
      simp only [e4polyPre, argOk, RAM_END, s1sp, s1a0, s1a1, canon4]
      refine ⟨by decide, by decide, ?_, fun i hi => ?_, by decide⟩
      · simp only [BitVec.reduceAdd, sy0, sy1, sy2, sy3]
        exact ⟨hy0, hy1, hy2, hy3⟩
      · rw [read_congr _ T.mem _ 4 (fun j hj => s1out _ (by right; rw [coeffs4_length] at hi; bv_omega))]
        exact htab i hi)
  replace hpc2 : S2.pc = S1.getReg 1#5 := hpc2
  replace hcs2 : ∀ i, calleeSaved i → S2.getReg i = S1.getReg i := hcs2
  replace hmem2 : ∀ a : Word, a.toNat + FEP < (S1.getReg 2#5).toNat ∨ (S1.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S1.getReg 10#5).toNat ∨ (S1.getReg 10#5).toNat + 16 ≤ a.toNat → S2.mem a = S1.mem a := hmem2
  rw [s1sp, s1a0] at hmem2
  simp only [e4polyPost, s1a0, s1a1] at hpost2
  obtain ⟨hcanE, hvalE⟩ := hpost2
  have hyl : limbsAt S1.mem 0x13fffa8#32 = ofLimbs (y0.toNat : F) (y1.toNat : F) (y2.toNat : F) (y3.toNat : F) := by
    simp only [limbsAt, BitVec.reduceAdd, sy0, sy1, sy2, sy3]
  rw [hyl] at hvalE
  have s2rom : ∀ b : Word, b.toNat < 4194304 → S2.mem b = T.mem b := fun b hb => by
    rw [hmem2 b (by left; bv_omega) (by left; bv_omega), s1rom b hb]
  have s2bl : ∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401100 → S2.mem a = T.mem a := fun a h1 h2' => by
    rw [hmem2 a (by right; bv_omega) (by right; bv_omega), s1out a (by right; omega)]
  have s2cs : ∀ r : Reg, calleeSaved r → (Main3.σ.reg r).val = r.toNat → S2.getReg r = T.getReg r := fun r h hv => by
    rw [hcs2 r h, j1 r (by rintro rfl; simp [calleeSaved] at h), hrel3.reg_same _ Main3.run r hv]
  have s2r : ∀ r : Reg, calleeSaved r → S2.getReg r = T3.getReg r := fun r h => by
    rw [hcs2 r h, j1 r (by rintro rfl; simp [calleeSaved] at h)]
  have s2sp : S2.getReg 2#5 = 0x13fff80#32 := (hcs2 _ (by rv_callee_saved)).trans s1sp
  have hpc2' : S2.pc = 0x38#32 + BitVec.ofNat 32 (4 * 34) := by rw [hpc2, hS1, jal_getReg1]; rfl
  ------------------------------------------------------------------ `blake2s_compress`
  have hc4 : CodeAt S2 (0x38#32 + BitVec.ofNat 32 (4 * 34)) ((Code.main.drop 34).take 34) :=
    codeAt_of_rom (hb4 ▸ codeAt_take (codeAt_drop hmain 34 (by rw [hlen]; bv_omega)) 34)
      (by simp [hl, ROM_END]) s2rom
  have s2spn : (S2.getReg 2#5).toNat = 0x13fff80 := by rw [s2sp]; rfl
  obtain ⟨T4, hrun4, hrel4, hrom4, hout4, hfr4⟩ := block_jal _ Main4.instrs Main4.σ S2 _ (Ab - 0x148#32) [rBl] []
    Main4.dec Main4.run hpc2' (by decide) (by simp [hl, ROM_END]) hc4 j4
    (by
      rw [show ((Code.main.drop 34).take 34).length = 34 by decide +kernel,
        read_congr S2.mem T.mem _ 4 (fun j hj => s2rom _ (by bv_omega)),
        show (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 68) by decide]
      exact (hmain 68 (by omega)).trans e68)
    dj4 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 34 (96 - 34) = 34 from rfl] at hrun4
  set S3 := (T4.setPC (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + (Ab - 0x148#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + 4) with hS3
  have j3' : ∀ r : Reg, r ≠ 1#5 → S3.getReg r = T4.getReg r := fun r hr => by rw [hS3, jal_getReg _ _ _ _ hr]
  have hpc3 : S3.pc = Ab := by rw [hS3, jal_pc]; bv_omega
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = T.mem b := fun b hb => by
    rw [hS3, jal_mem, hrom4 b (by simp only [ROM_END]; omega), s2rom b hb]
  have s3sp : S3.getReg 2#5 = 0x13fff80#32 := by
    rw [j3' _ (by decide), hrel4.reg_same _ Main4.run _ (by decide +kernel), s2sp]
  have s3a0 : S3.getReg 10#5 = 0x1401000#32 := by rw [j3' _ (by decide), hrel4.reg_cst 10#5 0x1401000#32 (by decide +kernel)]
  have s3a1 : S3.getReg 11#5 = 20#32 := by rw [j3' _ (by decide), hrel4.reg_cst 11#5 20#32 (by decide +kernel)]
  have s3a2 : S3.getReg 12#5 = 1#32 := by rw [j3' _ (by decide), hrel4.reg_cst 12#5 1#32 (by decide +kernel)]
  -- the evaluator before the call: the configured IV, the five input words, zeros
  have s3out : ∀ a : Word, (a.toNat < 0x1401000 ∨ 0x1401054 ≤ a.toNat) → S3.mem a = S2.mem a := fun a ha => by
    rw [hS3, jal_mem]
    apply hfr4 [⟨0, 0x1401000, 0x1401054, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, getReg_x0]; simp; omega
  have stc : ∀ (k : Word) (w : Word), outOK Main4.σ [rBl] [] 0 k = true →
      outNode Main4.σ 0 k < Main4.σ.pool.len → nodeAt Main4.σ.pool (outNode Main4.σ 0 k) = .const w →
      read S3.mem k 4 = w :=
    fun k w h hi hc => by
      have := hout4 0 k (by decide) h
      rw [getReg_x0, BitVec.zero_add] at this
      rw [hS3, jal_mem, this]; exact val_const Main4.wf _ _ w hi hc
  have stv : ∀ (k : Word) (i : Nat) (v : Word), outOK Main4.σ [rBl] [] 0 k = true → outNode Main4.σ 0 k = i →
      i < 32 → S2.getReg (BitVec.ofNat 5 i) = v → read S3.mem k 4 = v :=
    fun k i v h hn hi hv => by
      have := hout4 0 k (by decide) h
      rw [getReg_x0, BitVec.zero_add] at this
      rw [hS3, jal_mem, this, hn, val_init _ _ Main4.run S2 i hi, hv]
  have hzS3 : ∀ a : Word, 0x1401054 ≤ a.toNat → a.toNat < 0x1401100 → S3.mem a = 0 := fun a h1 h2' => by
    rw [s3out a (by right; omega), s2bl a (by omega) h2', hz a (by omega) h2']
  have rz : ∀ a : Word, 0x1401054 ≤ a.toNat → a.toNat + 4 ≤ 0x1401100 → read S3.mem a 4 = 0#32 := fun a h1 h2' => by
    rw [read_congr S3.mem (fun _ => 0) _ 4 (fun j hj => hzS3 _ (by bv_omega) (by bv_omega))]
    simp [read]
  obtain ⟨n4, U, hrun5, hpc5, hpost5, hcs5, hmem5⟩ := blake2s_compress_impl Ab S3 hpc3 (by simp)
    ⟨(by rw [hpc3]; exact codeAt_of_rom hbl (by simp only [ROM_END]; omega) s3rom),
      (by rw [hpc3]; exact hAb), (by rw [hpc3]; simp only [ROM_END]; omega),
      (by show (S3.getReg 1#5).toNat % 4 = 0; rw [hS3, jal_getReg1]; decide),
      (by show (S3.getReg 2#5).toNat % 16 = 0; rw [s3sp]; decide),
      (by show ROM_END + 160 ≤ (S3.getReg 2#5).toNat; rw [s3sp]; decide),
      (by show (S3.getReg 2#5).toNat ≤ RAM_END; rw [s3sp]; decide)⟩
    (by simp only [blakePre, s3a0, s3sp, s3a2, RAM_END]; decide)
  replace hpc5 : U.pc = S3.getReg 1#5 := hpc5
  replace hcs5 : ∀ i, calleeSaved i → U.getReg i = S3.getReg i := hcs5
  replace hmem5 : ∀ a : Word, a.toNat + 160 < (S3.getReg 2#5).toNat ∨ (S3.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S3.getReg 10#5).toNat ∨ (S3.getReg 10#5).toNat + 132 ≤ a.toNat → U.mem a = S3.mem a := hmem5
  rw [s3sp, s3a0] at hmem5
  simp only [blakePost, s3a0, s3a1, s3a2] at hpost5
  have hIV : wordsAt S3.mem 0x1401000#32 8 =
      Vector.ofFn fun i => IV i ^^^ (if i = 0 then 0x01010020#32 else 0#32) := by
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    · exact (stc _ 0x6b08e647#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0xbb67ae85#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x3c6ef372#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0xa54ff53a#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x510e527f#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x9b05688c#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x1f83d9ab#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x5be0cd19#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
  have hM : wordsAt S3.mem (0x1401000#32 + 64#32) 16 = #v[x, y0, y1, y2, y3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    · exact stv _ 20 _ (by decide +kernel) (by decide +kernel) (by decide)
        ((s2cs _ (by rv_callee_saved) (by decide +kernel)).trans h20)
    · exact stv _ 21 _ (by decide +kernel) (by decide +kernel) (by decide)
        ((s2cs _ (by rv_callee_saved) (by decide +kernel)).trans h21)
    · exact stv _ 22 _ (by decide +kernel) (by decide +kernel) (by decide)
        ((s2cs _ (by rv_callee_saved) (by decide +kernel)).trans h22)
    · exact stv _ 23 _ (by decide +kernel) (by decide +kernel) (by decide)
        ((s2cs _ (by rv_callee_saved) (by decide +kernel)).trans h23)
    · exact stv _ 24 _ (by decide +kernel) (by decide +kernel) (by decide)
        ((s2cs _ (by rv_callee_saved) (by decide +kernel)).trans h24)
    all_goals exact rz _ (by decide) (by decide)
  have ht : read S3.mem (0x1401000#32 + 128#32) 4 = 0#32 := rz _ (by decide) (by decide)
  rw [hIV, hM, ht] at hpost5
  -- `e` (the `ext4_poly` result) at `sp + 8`: untouched since
  have ue : ∀ a : Word, 0x13fff88 ≤ a.toNat → a.toNat < 0x13fff98 → U.mem a = S2.mem a := fun a h1 h2' => by
    rw [hmem5 a (by right; bv_omega) (by left; bv_omega), s3out a (by left; omega)]
  have ur : ∀ k : Word, k.toNat ≤ 12 → read U.mem (0x13fff88#32 + k) 4 = read S2.mem (0x13fff88#32 + k) 4 :=
    fun k hk => read_congr _ _ _ _ (fun j hj => ue _ (by bv_omega) (by bv_omega))
  have u0 : read U.mem 0x13fff88#32 4 = read S2.mem 0x13fff88#32 4 :=
    read_congr _ _ _ _ (fun j hj => ue _ (by bv_omega) (by bv_omega))
  have utab : ∀ a : Word, 0x1400190 ≤ a.toNat → a.toNat < 0x1400390 → U.mem a = T.mem a := fun a h1 h2' => by
    rw [hmem5 a (by right; bv_omega) (by left; bv_omega), s3out a (by left; omega),
      hmem2 a (by right; bv_omega) (by right; bv_omega), s1out a (by right; omega)]
  refine ⟨_, U, run_trans (run_trans (run_trans hrun3 hrun2) hrun4) hrun5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => ?_, ?_⟩
  · rw [hpc5, hS3, jal_getReg1]; decide
  · rw [hcs5 _ (by rv_callee_saved), s3sp]
  · rw [hcs5 _ (by rv_callee_saved), j3' _ (by decide), hrel4.reg_same _ Main4.run _ (by decide +kernel),
      s2cs _ (by rv_callee_saved) (by decide +kernel), h9]
  · rw [hcs5 _ (by rv_callee_saved), j3' _ (by decide), hrel4.reg_same _ Main4.run _ (by decide +kernel),
      s2r _ (by rv_callee_saved), hrel3.reg_var _ Main3.run _ 10 (by decide) (by decide +kernel)]
    exact h10
  · rw [hcs5 _ (by rv_callee_saved), j3' _ (by decide), hrel4.reg_cst 19#5 0x1401000#32 (by decide +kernel)]
  · simp only [canon4] at hcanE ⊢
    rw [u0, ur 4#32 (by decide), ur 8#32 (by decide), ur 12#32 (by decide)]; exact hcanE
  · simp only [limbsAt] at hvalE ⊢
    rw [u0, ur 4#32 (by decide), ur 8#32 (by decide), ur 12#32 (by decide)]; exact hvalE
  · rw [hpost5.1]; rfl
  · rw [read_congr _ T.mem _ 4 (fun j hj => utab _ (by rw [coeffs4_length] at hi; bv_omega)
      (by rw [coeffs4_length] at hi; bv_omega))]
    exact htab i hi
  · intro b hb
    rw [hmem5 b (by left; bv_omega) (by left; bv_omega), s3rom b hb]

end RV
