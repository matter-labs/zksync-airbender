import Slop.RV.CopyRun
import Slop.RV.CallW
import Slop.RV.BlakeDeleg.Rounds
import Slop.Block.Block
import Slop.RV.BlakeDeleg.ImplRuns
import Slop.RV.Code.blake2s_compress_mop

/-! `blake2s_compress(st, len, last)` by Airbender's round-function delegation (`blake2_with_compression`): the
counter and last-block words into the extended state, seven calls of CSR `0x7c7` (`blake_calls`), return. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

/-- The evaluator (state +0, extended state +32, block +128, counter +192) 128-aligned in RAM above `sp`, `last` a
`bool`. -/
def blakeDPre (s : State) : Prop :=
  (s.getReg 10#5).toNat % 128 = 0 ∧ (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat ∧
  (s.getReg 10#5).toNat + 196 ≤ RAM_END ∧ (s.getReg 12#5 = 0#32 ∨ s.getReg 12#5 = 1#32)

/-- The state becomes the compression of the block, with the counter advanced by `len`. -/
def blakeDPost (s s' : State) : Prop :=
  readWords s'.mem (s.getReg 10#5) 8 =
    compress (readWords s.mem (s.getReg 10#5) 8) (readWords s.mem (s.getReg 10#5 + 128#32) 16)
      (read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5) (s.getReg 12#5 = 1#32) ∧
  read s'.mem (s.getReg 10#5 + 192#32) 4 = read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5

theorem blake2s_compress_mop_impl (A : Word) :
    ImplementsAtW A Code.blake2s_compress_mop [] 16 blakeDPre 196 blakeDPost := by
  intro s hentry _ ⟨hcode, hal, hrom, hra, hsp, hlo, hhi⟩ ⟨h128, hspa, hR, hl⟩
  rw [hentry] at hcode hal hrom
  replace hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  replace hsp : (s.getReg 2#5).toNat % 16 = 0 := hsp
  replace hlo : ROM_END + 16 ≤ (s.getReg 2#5).toNat := hlo
  have hL : Code.blake2s_compress_mop.length = 29 := rfl
  have hlo' := hlo
  have hR' := hR
  simp only [ROM_END, RAM_END] at hlo' hR'
  -- words 0 … 17: the frame, the counter advanced by `len` at `a0 + 192`, the counter and last-block words of the
  -- extended state at `a0 + 80`, `a0 + 88`, the calls' arguments
  obtain ⟨S, hrun1, hpc1, -, hrel1, hrom1, hout1, hfr1⟩ := block_at Code.blake2s_compress_mop 0 18 BDPro.instrs
    BDPro.σ s A [⟨2, -8, 0, 4⟩, ⟨10, 80, 96, 4⟩, ⟨10, 192, 196, 4⟩] [(⟨2, -8, 0, 4⟩, ⟨10, 80, 96, 4⟩), (⟨2, -8, 0, 4⟩, ⟨10, 192, 196, 4⟩)]
    BDPro.dec BDPro.run (by rw [hL]; omega) (by rw [hentry]; simp) hal hrom hcode (by sym_side) (by sym_side)
    (by decide +kernel)
  have mS : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (s.getReg 10#5).toNat + 80 ∨ (s.getReg 10#5).toNat + 96 ≤ a.toNat →
      a.toNat < (s.getReg 10#5).toNat + 192 ∨ (s.getReg 10#5).toNat + 196 ≤ a.toNat → S.mem a = s.mem a :=
    fun a h1 h2 h3 => hfr1 [⟨2, -8, 0, 1⟩, ⟨10, 80, 96, 1⟩, ⟨10, 192, 196, 1⟩] (by decide +kernel) (by sym_side) a
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.Outside]; omega)
  have sv : ∀ (k : Word) (r : Nat), r < 32 →
      outOK BDPro.σ [⟨2, -8, 0, 4⟩, ⟨10, 80, 96, 4⟩, ⟨10, 192, 196, 4⟩] [(⟨2, -8, 0, 4⟩, ⟨10, 80, 96, 4⟩), (⟨2, -8, 0, 4⟩, ⟨10, 192, 196, 4⟩)] 2 k = true →
      outNode BDPro.σ 2 k = r → read S.mem (s.getReg 2#5 + k) 4 = s.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by rw [hout1 2 k (by decide) hok, hn]; exact val_init BDPro.instrs BDPro.σ BDPro.run s r hr
  have hcnt : read S.mem (s.getReg 10#5 + 192#32) 4 = read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5 := by
    rw [hout1 10 192#32 (by decide) (by decide +kernel)]
    sym_unfold
    simp only [ctxOf, alu, ite_true, Nat.reduceMul, BitVec.setWidth_eq, BitVec.signExtend_eq]
    exact BitVec.add_comm _ _
  have h80 : read S.mem (s.getReg 10#5 + 80#32) 4 =
      (read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5) ^^^ 0x510e527f#32 := by
    rw [hout1 10 80#32 (by decide) (by decide +kernel)]
    sym_unfold
    simp only [ctxOf, alu, ite_true, Nat.reduceMul, BitVec.setWidth_eq, BitVec.signExtend_eq]
    rw [BitVec.add_comm]
  have h88 : read S.mem (s.getReg 10#5 + 88#32) 4 = (0#32 - s.getReg 12#5) ^^^ 0x1f83d9ab#32 := by
    rw [hout1 10 88#32 (by decide) (by decide +kernel)]
    sym_unfold
    simp only [ctxOf, alu]
  have s1r : ∀ r : Reg, (BDPro.σ.reg r).val = r.toNat → S.getReg r = s.getReg r := fun r h =>
    Rel.reg_same BDPro.instrs BDPro.run hrel1 r h
  have s2 : S.getReg 2#5 = s.getReg 2#5 + 4294967280#32 :=
    Rel.reg_addr BDPro.instrs BDPro.run hrel1 2#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)
  -- words 18 … 24: the seven calls
  have hcS := codeAt_of_rom hcode hrom hrom1
  obtain ⟨T, hrunT, tpc, -, -, trr, -, th, tm⟩ := blake_calls S (s.getReg 10#5) (by simp only [ROM_END]; omega) h128
    (by simp only [RAM_END]; omega) (s1r _ (by decide +kernel))
    (Rel.reg_addr BDPro.instrs BDPro.run hrel1 11#5 10 _ (by decide) (by decide +kernel) (by decide +kernel))
    ((Rel.reg_cst hrel1 12#5 0x90000#32 (by decide +kernel)).trans (by decide)) (by rw [hpc1]; bv_omega)
    (by rw [hpc1]; simp only [ROM_END] at hrom ⊢; rw [hL] at hrom; bv_omega)
    (fun k hk => by
      rw [show S.pc + BitVec.ofNat 32 (4 * k) = A + BitVec.ofNat 32 (4 * (18 + k)) by rw [hpc1]; bv_omega,
        hcS (18 + k) (by rw [hL]; omega)]
      interval_cases k <;> rfl) 7 le_rfl
  have tS : ∀ b : Word, b.toNat + 4 ≤ (s.getReg 10#5).toNat → read T.mem b 4 = read S.mem b 4 := fun b hb =>
    read_of_outside tm b 4 ⟨Or.inl hb, by omega⟩
  have t2 : T.getReg 2#5 = s.getReg 2#5 + 4294967280#32 := (trr 2 (by decide)).trans s2
  have t2n : (T.getReg 2#5).toNat = (s.getReg 2#5).toNat - 16 := by rw [t2]; bv_omega
  -- words 25 … 28: `ra`, `s0` back, `sp` up, `ret`
  obtain ⟨U, hrunU, upc, hrelU, -, -, -⟩ := block_ret (C := Code.blake2s_compress_mop) 25 3 BDEpi.instrs BDEpi.σ
    [⟨2, 8, 16, 4⟩] [] BDEpi.dec BDEpi.run (by rw [hL]; omega) (by rw [tpc, hpc1]; bv_omega) hal hrom
    (codeAt_of_rom hcode hrom (fun b hb => by rw [tm b (Or.inl (by simp only [ROM_END] at hb; omega)), hrom1 b hb]))
    rfl (by sym_side) (by simp) (by decide +kernel) (fun S' h => by
      rw [Rel.reg_load BDEpi.instrs BDEpi.run h 1#5 2 12#32 (by decide) (by decide +kernel) (by decide +kernel),
        tS _ (by rw [t2]; bv_omega), t2, show s.getReg 2#5 + 4294967280#32 + 12#32 = s.getReg 2#5 + 4294967292#32 by
          bv_omega, sv _ 1 (by decide) (by decide +kernel) (by decide +kernel)]
      exact hra)
  have um : U.mem = T.mem := Rel.mem_nil hrelU (by decide +kernel)
  have ur : ∀ r : Reg, (BDEpi.σ.reg r).val = r.toNat → U.getReg r = T.getReg r := fun r h =>
    Rel.reg_same BDEpi.instrs BDEpi.run hrelU r h
  have u1 : U.getReg 1#5 = s.getReg 1#5 := by
    rw [Rel.reg_load BDEpi.instrs BDEpi.run hrelU 1#5 2 12#32 (by decide) (by decide +kernel) (by decide +kernel),
      tS _ (by rw [t2]; bv_omega), t2, show s.getReg 2#5 + 4294967280#32 + 12#32 = s.getReg 2#5 + 4294967292#32 by
        bv_omega, sv _ 1 (by decide) (by decide +kernel) (by decide +kernel)]
  -- the evaluator as the calls found it: the counter and last-block words written, nothing else of it changed
  have rS : ∀ b : Word, (s.getReg 10#5).toNat ≤ b.toNat → b.toNat + 4 ≤ (s.getReg 10#5).toNat + 192 →
      (b.toNat + 4 ≤ (s.getReg 10#5).toNat + 80 ∨ (s.getReg 10#5).toNat + 96 ≤ b.toNat) →
      read S.mem b 4 = read s.mem b 4 := fun b h1 h2 h3 =>
    read_congr _ _ _ _ (fun j hj => mS _ (by right; bv_omega) (by bv_omega) (by left; bv_omega))
  have hS : readWords S.mem (s.getReg 10#5) 8 = readWords s.mem (s.getReg 10#5) 8 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    exact rS _ (by bv_omega) (by bv_omega) (by left; bv_omega)
  have mS16 : readWords S.mem (s.getReg 10#5 + 128#32) 16 = readWords s.mem (s.getReg 10#5 + 128#32) 16 := by
    apply Vector.ext; intro i hi
    simp only [readWords, Vector.getElem_ofFn]
    exact rS _ (by bv_omega) (by bv_omega) (by right; bv_omega)
  have e12 : (readWords S.mem (s.getReg 10#5 + 32#32) 16)[12] =
      (read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5) ^^^ IV 4 := by
    simp only [readWords, Vector.getElem_ofFn]
    rw [show s.getReg 10#5 + 32#32 + BitVec.ofNat 32 (4 * 12) = s.getReg 10#5 + 80#32 by bv_omega, h80]; rfl
  have e14 : (readWords S.mem (s.getReg 10#5 + 32#32) 16)[14] =
      (if decide (s.getReg 12#5 = 1#32) = true then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by
    simp only [readWords, Vector.getElem_ofFn]
    rw [show s.getReg 10#5 + 32#32 + BitVec.ofNat 32 (4 * 14) = s.getReg 10#5 + 88#32 by bv_omega, h88]
    rcases hl with h | h <;> rw [h] <;> rfl
  refine ⟨18 + 7 + 4, U, run_trans (run_trans hrun1 hrunT) hrunU, upc.trans u1, ⟨?_, ?_⟩, ?_, fun a ha hb => ?_⟩
  · rw [um, th]; simp only [↓reduceIte]; rw [compress_eq _ _ _ _ _ e12 e14, hS, mS16]
  · rw [um, read_of_outside tm _ _ ⟨Or.inr (by bv_omega), by bv_omega⟩, hcnt]
  · refine calleeSaved_all _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [Rel.reg_addr BDEpi.instrs BDEpi.run hrelU 2#5 2 16#32 (by decide) (by decide +kernel) (by decide +kernel), t2]
      bv_omega
    · rw [Rel.reg_load BDEpi.instrs BDEpi.run hrelU 8#5 2 8#32 (by decide) (by decide +kernel) (by decide +kernel),
        tS _ (by rw [t2]; bv_omega), t2, show s.getReg 2#5 + 4294967280#32 + 8#32 = s.getReg 2#5 + 4294967288#32 by
          bv_omega, sv _ 8 (by decide) (by decide +kernel) (by decide +kernel)]
    all_goals exact (ur _ (by decide +kernel)).trans ((trr _ (by decide)).trans (s1r _ (by decide +kernel)))
  · replace ha : a.toNat + 16 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat := ha
    replace hb : a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 196 ≤ a.toNat := hb
    rw [um, tm a (by omega), mS a (by omega) (by omega) (by omega)]

end RV
