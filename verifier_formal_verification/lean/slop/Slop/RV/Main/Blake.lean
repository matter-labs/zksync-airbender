import Slop.RV.Main.A
import Slop.RV.Blake.Impl
import Slop.RV.BlakeDeleg.Impl

/-! `main`, the Blake2s part: from `main + 0x88` to `main + 0x14c`, the evaluator `BLAKE` (`0x1401000`, zero at
start) set up with the configured IV and the five input words (`s4 … s8`), then `blake2s_compress(BLAKE, 20, true)`.
`MainBlakeOK` is what the rest of `main` needs; `main_blake` proves it for the baseline Blake2s (plain Rust), and
`main_blake_deleg` for the delegation. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 0

/-- From `main + 0x88` (the code of `main` and of `blake2s_compress` in place, `sp = 0x13fff80`, `BLAKE` zero), the
run reaches `main + 0x14c` with `s3 = BLAKE` holding the Blake2s digest of `s4 … s8`; other callee-saved registers,
memory above `sp` outside `BLAKE`, and ROM unchanged. -/
def MainBlakeOK (codeM codeB : List Word) (Ab : Word) : Prop :=
  ∀ S : State, S.pc = 0xc0#32 → CodeAt S 0x38#32 codeM → CodeAt S Ab codeB → S.getReg 2#5 = 0x13fff80#32 →
    (∀ a : Word, 0x1401000 ≤ a.toNat → a.toNat < 0x1401100 → S.mem a = 0) →
    ∃ m U, run m S = some U ∧ U.pc = 0x14c#32 ∧ U.getReg 19#5 = 0x1401000#32 ∧
      (∀ r, calleeSaved r → r ≠ 19#5 → U.getReg r = S.getReg r) ∧
      wordsAt U.mem 0x1401000#32 8 =
        blake5 #v[S.getReg 20#5, S.getReg 21#5, S.getReg 22#5, S.getReg 23#5, S.getReg 24#5] ∧
      (∀ a : Word, 0x13fff80 ≤ a.toNat → (a.toNat < 0x1401000 ∨ 0x1401100 ≤ a.toNat) → U.mem a = S.mem a) ∧
      (∀ b : Word, b.toNat < ROM_END → U.mem b = S.mem b)

namespace MainBl
abbrev rBl : Region := ⟨0, 0x1401000, 0x1401054, 4⟩
abbrev rBlD : Region := ⟨0, 0x1401000, 0x1401094, 4⟩
end MainBl
open MainBl

theorem val_const {p : Pool} (hw : p.WF) (c : Ctx) (i : Nat) (w : Word) (hi : i < p.len)
    (h : nodeAt p i = .const w) : p.val c i = w := by
  rw [(nodeAt_spec c p hw i hi).2, h]; rfl

/-- The baseline Blake2s (`Code.blake2s_compress`, state +0, block +64, counter +128). -/
theorem main_blake (codeM : List Word) (Ab : Word) (hlen : codeM.length = 96)
    (hAb : Ab.toNat % 4 = 0) (hAbr : Ab.toNat + 4 * Code.blake2s_compress.length ≤ 4194304)
    (hb4 : (codeM.drop 34).take 34 = (Code.main.drop 34).take 34)
    (j4 : Word) (hj4 : codeM[68]? = some j4) (dj4 : decode j4 = some (.jal 1#5 (Ab - 0x148#32))) :
    MainBlakeOK codeM Code.blake2s_compress Ab := by
  intro S2 hpc2' hmain hbl s2sp hz
  have hl : Code.main.length = 96 := by decide +kernel
  obtain ⟨_, e68⟩ := List.getElem?_eq_some_iff.mp hj4
  simp only [ROM_END, RAM_END] at *
  have hpc2 : S2.pc = 0x38#32 + BitVec.ofNat 32 (4 * 34) := by rw [hpc2']; rfl
  have hc4 : CodeAt S2 (0x38#32 + BitVec.ofNat 32 (4 * 34)) ((Code.main.drop 34).take 34) :=
    hb4 ▸ codeAt_take (codeAt_drop hmain 34 (by rw [hlen]; bv_omega)) 34
  have s2spn : (S2.getReg 2#5).toNat = 0x13fff80 := by rw [s2sp]; rfl
  obtain ⟨T4, hrun4, hrel4, hrom4, hout4, hfr4⟩ := block_jal _ Main4.instrs Main4.σ S2 _ (Ab - 0x148#32) [rBl] []
    Main4.dec Main4.run hpc2 (by decide) (by simp [hl, ROM_END]) hc4 j4
    (by
      rw [show ((Code.main.drop 34).take 34).length = 34 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 68) by decide]
      exact (hmain 68 (by omega)).trans e68)
    dj4 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 34 (96 - 34) = 34 from rfl] at hrun4
  set S3 := (T4.setPC (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + (Ab - 0x148#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + 4) with hS3
  have j3' : ∀ r : Reg, r ≠ 1#5 → S3.getReg r = T4.getReg r := fun r hr => by rw [hS3, jal_getReg _ _ _ _ hr]
  have hpc3 : S3.pc = Ab := by rw [hS3, jal_pc]; bv_omega
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = S2.mem b := fun b hb => by
    rw [hS3, jal_mem, hrom4 b (by simp only [ROM_END]; omega)]
  have s3sp : S3.getReg 2#5 = 0x13fff80#32 := by
    rw [j3' _ (by decide), hrel4.reg_same _ Main4.run _ (by decide +kernel), s2sp]
  have s3a0 : S3.getReg 10#5 = 0x1401000#32 := by rw [j3' _ (by decide), hrel4.reg_cst 10#5 0x1401000#32 (by decide +kernel)]
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
  have stv : ∀ (k : Word) (i : Nat), outOK Main4.σ [rBl] [] 0 k = true → outNode Main4.σ 0 k = i →
      i < 32 → read S3.mem k 4 = S2.getReg (BitVec.ofNat 5 i) :=
    fun k i h hn hi => by
      have := hout4 0 k (by decide) h
      rw [getReg_x0, BitVec.zero_add] at this
      rw [hS3, jal_mem, this, hn, val_init _ _ Main4.run S2 i hi]
  have hzS3 : ∀ a : Word, 0x1401054 ≤ a.toNat → a.toNat < 0x1401100 → S3.mem a = 0 := fun a h1 h2' => by
    rw [s3out a (by right; omega), hz a (by omega) h2']
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
  have s3a1 : S3.getReg 11#5 = 20#32 := by rw [j3' _ (by decide), hrel4.reg_cst 11#5 20#32 (by decide +kernel)]
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
  have hM : wordsAt S3.mem (0x1401000#32 + 64#32) 16 =
      #v[S2.getReg 20#5, S2.getReg 21#5, S2.getReg 22#5, S2.getReg 23#5, S2.getReg 24#5, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0] := by
    apply Vector.ext; intro i hi
    simp only [wordsAt, Vector.getElem_ofFn]
    interval_cases i
    · exact stv _ 20 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 21 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 22 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 23 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 24 (by decide +kernel) (by decide +kernel) (by decide)
    all_goals exact rz _ (by decide) (by decide)
  have ht : read S3.mem (0x1401000#32 + 128#32) 4 = 0#32 := rz _ (by decide) (by decide)
  rw [hIV, hM, ht] at hpost5
  refine ⟨_, U, run_trans hrun4 hrun5, ?_, ?_, fun r hr h19 => ?_, ?_, fun a h1 h2' => ?_, fun b hb => ?_⟩
  · rw [hpc5, hS3, jal_getReg1]; decide
  · rw [hcs5 _ (by rv_callee_saved), j3' _ (by decide), hrel4.reg_cst 19#5 0x1401000#32 (by decide +kernel)]
  · rw [hcs5 r hr, j3' r (by rintro rfl; simp [calleeSaved] at hr), hrel4.reg_same _ Main4.run r ?_]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      first | decide +kernel | exact absurd rfl h19
  · rw [hpost5.1]; rfl
  · rw [hmem5 a (by right; bv_omega) (by rcases h2' with h | h <;> [left; right] <;> bv_omega),
      s3out a (by rcases h2' with h | h <;> [left; right] <;> omega)]
  · rw [hmem5 b (by left; bv_omega) (by left; bv_omega), s3rom b hb]

/-- Blake2s by the round-function delegation (`Code.blake2s_compress_mop`, state +0, extended state +32, block +128,
counter +192). -/
theorem main_blake_deleg (codeM : List Word) (Ab : Word) (hlen : codeM.length = 96)
    (hAb : Ab.toNat % 4 = 0) (hAbr : Ab.toNat + 4 * Code.blake2s_compress_mop.length ≤ 4194304)
    (hb4 : (codeM.drop 34).take 34 = (Code.main_mop.drop 34).take 34)
    (j4 : Word) (hj4 : codeM[68]? = some j4) (dj4 : decode j4 = some (.jal 1#5 (Ab - 0x148#32))) :
    MainBlakeOK codeM Code.blake2s_compress_mop Ab := by
  intro S2 hpc2' hmain hbl s2sp hz
  have hl : Code.main_mop.length = 96 := by decide +kernel
  obtain ⟨_, e68⟩ := List.getElem?_eq_some_iff.mp hj4
  simp only [ROM_END, RAM_END] at *
  have hpc2 : S2.pc = 0x38#32 + BitVec.ofNat 32 (4 * 34) := by rw [hpc2']; rfl
  have hc4 : CodeAt S2 (0x38#32 + BitVec.ofNat 32 (4 * 34)) ((Code.main_mop.drop 34).take 34) :=
    hb4 ▸ codeAt_take (codeAt_drop hmain 34 (by rw [hlen]; bv_omega)) 34
  have s2spn : (S2.getReg 2#5).toNat = 0x13fff80 := by rw [s2sp]; rfl
  obtain ⟨T4, hrun4, hrel4, hrom4, hout4, hfr4⟩ := block_jal _ Main4D.instrs Main4D.σ S2 _ (Ab - 0x148#32) [rBlD] []
    Main4D.dec Main4D.run hpc2 (by decide) (by simp [hl, ROM_END]) hc4 j4
    (by
      rw [show ((Code.main_mop.drop 34).take 34).length = 34 by decide +kernel,
        show (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) : Word) =
          0x38#32 + BitVec.ofNat 32 (4 * 68) by decide]
      exact (hmain 68 (by omega)).trans e68)
    dj4 (by simp; bv_omega) (by sym_side) (by simp) (by decide +kernel)
  simp only [List.length_take, List.length_drop, hl, show min 34 (96 - 34) = 34 from rfl] at hrun4
  set S3 := (T4.setPC (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + (Ab - 0x148#32))).setReg 1#5
    (0x38#32 + BitVec.ofNat 32 (4 * 34) + BitVec.ofNat 32 (4 * 34) + 4) with hS3
  have j3' : ∀ r : Reg, r ≠ 1#5 → S3.getReg r = T4.getReg r := fun r hr => by rw [hS3, jal_getReg _ _ _ _ hr]
  have hpc3 : S3.pc = Ab := by rw [hS3, jal_pc]; bv_omega
  have s3rom : ∀ b : Word, b.toNat < 4194304 → S3.mem b = S2.mem b := fun b hb => by
    rw [hS3, jal_mem, hrom4 b (by simp only [ROM_END]; omega)]
  have s3sp : S3.getReg 2#5 = 0x13fff80#32 := by
    rw [j3' _ (by decide), hrel4.reg_same _ Main4D.run _ (by decide +kernel), s2sp]
  have s3a0 : S3.getReg 10#5 = 0x1401000#32 := by rw [j3' _ (by decide), hrel4.reg_cst 10#5 0x1401000#32 (by decide +kernel)]
  have s3a2 : S3.getReg 12#5 = 1#32 := by rw [j3' _ (by decide), hrel4.reg_cst 12#5 1#32 (by decide +kernel)]
  -- the evaluator before the call: the configured IV, the five input words, zeros
  have s3out : ∀ a : Word, (a.toNat < 0x1401000 ∨ 0x1401094 ≤ a.toNat) → S3.mem a = S2.mem a := fun a ha => by
    rw [hS3, jal_mem]
    apply hfr4 [⟨0, 0x1401000, 0x1401094, 1⟩] (by decide +kernel) (by sym_side) a
    intro R hR; simp only [List.mem_singleton] at hR; subst hR
    simp only [Region.Outside, getReg_x0]; simp; omega
  have stc : ∀ (k : Word) (w : Word), outOK Main4D.σ [rBlD] [] 0 k = true →
      outNode Main4D.σ 0 k < Main4D.σ.pool.len → nodeAt Main4D.σ.pool (outNode Main4D.σ 0 k) = .const w →
      read S3.mem k 4 = w :=
    fun k w h hi hc => by
      have := hout4 0 k (by decide) h
      rw [getReg_x0, BitVec.zero_add] at this
      rw [hS3, jal_mem, this]; exact val_const Main4D.wf _ _ w hi hc
  have stv : ∀ (k : Word) (i : Nat), outOK Main4D.σ [rBlD] [] 0 k = true → outNode Main4D.σ 0 k = i →
      i < 32 → read S3.mem k 4 = S2.getReg (BitVec.ofNat 5 i) :=
    fun k i h hn hi => by
      have := hout4 0 k (by decide) h
      rw [getReg_x0, BitVec.zero_add] at this
      rw [hS3, jal_mem, this, hn, val_init _ _ Main4D.run S2 i hi]
  have hzS3 : ∀ a : Word, 0x1401094 ≤ a.toNat → a.toNat < 0x1401100 → S3.mem a = 0 := fun a h1 h2' => by
    rw [s3out a (by right; omega), hz a (by omega) h2']
  have rz : ∀ a : Word, 0x1401094 ≤ a.toNat → a.toNat + 4 ≤ 0x1401100 → read S3.mem a 4 = 0#32 := fun a h1 h2' => by
    rw [read_congr S3.mem (fun _ => 0) _ 4 (fun j hj => hzS3 _ (by bv_omega) (by bv_omega))]
    simp [read]
  obtain ⟨n4, U, hrun5, hpc5, hpost5, hcs5, hmem5⟩ := blake2s_compress_mop_impl Ab S3 hpc3 (by simp)
    ⟨(by rw [hpc3]; exact codeAt_of_rom hbl (by simp only [ROM_END]; omega) s3rom),
      (by rw [hpc3]; exact hAb), (by rw [hpc3]; simp only [ROM_END]; omega),
      (by show (S3.getReg 1#5).toNat % 4 = 0; rw [hS3, jal_getReg1]; decide),
      (by show (S3.getReg 2#5).toNat % 16 = 0; rw [s3sp]; decide),
      (by show ROM_END + 16 ≤ (S3.getReg 2#5).toNat; rw [s3sp]; decide),
      (by show (S3.getReg 2#5).toNat ≤ RAM_END; rw [s3sp]; decide)⟩
    (by simp only [blakeDPre, s3a0, s3sp, s3a2, RAM_END]; decide)
  replace hpc5 : U.pc = S3.getReg 1#5 := hpc5
  replace hcs5 : ∀ i, calleeSaved i → U.getReg i = S3.getReg i := hcs5
  replace hmem5 : ∀ a : Word, a.toNat + 16 < (S3.getReg 2#5).toNat ∨ (S3.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (S3.getReg 10#5).toNat ∨ (S3.getReg 10#5).toNat + 196 ≤ a.toNat → U.mem a = S3.mem a := hmem5
  rw [s3sp, s3a0] at hmem5
  have s3a1 : S3.getReg 11#5 = 20#32 := by rw [j3' _ (by decide), hrel4.reg_cst 11#5 20#32 (by decide +kernel)]
  simp only [blakeDPost, s3a0, s3a1, s3a2] at hpost5
  have hIV : readWords S3.mem 0x1401000#32 8 =
      Vector.ofFn fun i => IV i ^^^ (if i = 0 then 0x01010020#32 else 0#32) := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    interval_cases i
    · exact (stc _ 0x6b08e647#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0xbb67ae85#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x3c6ef372#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0xa54ff53a#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x510e527f#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x9b05688c#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x1f83d9ab#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
    · exact (stc _ 0x5be0cd19#32 (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (by revert hi; decide)
  have hM : readWords S3.mem (0x1401000#32 + 128#32) 16 =
      #v[S2.getReg 20#5, S2.getReg 21#5, S2.getReg 22#5, S2.getReg 23#5, S2.getReg 24#5, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0] := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    interval_cases i
    · exact stv _ 20 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 21 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 22 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 23 (by decide +kernel) (by decide +kernel) (by decide)
    · exact stv _ 24 (by decide +kernel) (by decide +kernel) (by decide)
    all_goals exact rz _ (by decide) (by decide)
  have ht : read S3.mem (0x1401000#32 + 192#32) 4 = 0#32 := rz _ (by decide) (by decide)
  rw [hIV, hM, ht] at hpost5
  refine ⟨_, U, run_trans hrun4 hrun5, ?_, ?_, fun r hr h19 => ?_, ?_, fun a h1 h2' => ?_, fun b hb => ?_⟩
  · rw [hpc5, hS3, jal_getReg1]; decide
  · rw [hcs5 _ (by rv_callee_saved), j3' _ (by decide), hrel4.reg_cst 19#5 0x1401000#32 (by decide +kernel)]
  · rw [hcs5 r hr, j3' r (by rintro rfl; simp [calleeSaved] at hr), hrel4.reg_same _ Main4D.run r ?_]
    rcases calleeSaved_cases r hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      first | decide +kernel | exact absurd rfl h19
  · exact hpost5.1
  · rw [hmem5 a (by right; bv_omega) (by rcases h2' with h | h <;> [left; right] <;> bv_omega),
      s3out a (by rcases h2' with h | h <;> [left; right] <;> omega)]
  · rw [hmem5 b (by left; bv_omega) (by left; bv_omega), s3rom b hb]

end RV
