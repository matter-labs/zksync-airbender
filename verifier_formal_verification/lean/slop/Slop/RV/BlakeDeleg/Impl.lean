import Slop.RV.Tactic
import Slop.RV.CopyRun
import Slop.RV.CallW
import Slop.RV.BlakeDeleg.Rounds
import Slop.RV.Code.blake2s_compress_mop

/-! `blake2s_compress(st, len, last)` by Airbender's round-function delegation (`blake2_with_compression`): the
counter and last-block words into the extended state, seven calls of CSR `0x7c7` (`blake_calls`), return. -/

namespace RV
open Spec
set_option maxHeartbeats 0
set_option maxRecDepth 100000

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
  intro s hentry _ hcall hpre
  unfold ReturnsW
  rw [Call, hentry] at hcall
  obtain ⟨h128, hspa, hR, hl⟩ := hpre
  simp only [RAM_END] at hR
  rv_start Code.blake2s_compress_mop hcall
  rv_steps 18 with hentry
  rv_cut
  have srom : ∀ b : Word, b.toNat < ROM_END → S.mem b = s.mem b := fun b hb => by
    simp only [ROM_END] at hb
    rw [cut_mem]
    repeat rw [write_outside (h := Or.inl (by bv_omega)) (ha := by bv_omega)]
  have hlen : Code.blake2s_compress_mop.length = 29 := rfl
  have hcS := codeAt_of_rom hcode (by rw [hlen]; simp only [ROM_END]; omega) srom
  obtain ⟨T, hrunT, hT⟩ := blake_calls S (s.getReg 10#5) (by simp only [ROM_END]; omega) h128
    (by simp only [RAM_END]; omega) cut_r10 cut_r11 (cut_r12.trans (by decide))
    (by rw [cut_pc]; bv_omega) (by rw [cut_pc]; simp only [ROM_END]; bv_omega)
    (fun k hk => by
      have := hcS (18 + k) (by rw [hlen]; omega)
      rw [show S.pc + BitVec.ofNat 32 (4 * k) = A + BitVec.ofNat 32 (4 * (18 + k)) by rw [cut_pc, hentry]; bv_omega,
        this]
      interval_cases k <;> rfl) 7 le_rfl
  apply run_of_run S T 7 _ hrunT
  obtain ⟨tpc, -, t12, trr, tv, th, tm⟩ := hT
  have tpc' : T.pc = A + 100#32 := by rw [tpc, cut_pc, hentry]; bv_omega
  rv_steps 4 with tpc', trr, read_of_outside tm, cut_r1, cut_r2, cut_r8
  rv_ret
  refine ⟨?_, ?_, ?_, ?_⟩
  · rv_regs
  · simp only [blakeDPost, set_mem, jump_mem, next_mem]
    -- the evaluator as the calls found it: the counter and last-block words written, nothing else of it changed
    have rS : ∀ b : Word, (s.getReg 10#5).toNat ≤ b.toNat → b.toNat + 4 ≤ (s.getReg 10#5).toNat + 192 →
        (b.toNat + 4 ≤ (s.getReg 10#5).toNat + 80 ∨ (s.getReg 10#5).toNat + 96 ≤ b.toNat) →
        read S.mem b 4 = read s.mem b 4 := by
      intro b h1 h2 h3
      rw [cut_mem]
      repeat rw [read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega)]
    have hS : readWords S.mem (s.getReg 10#5) 8 = readWords s.mem (s.getReg 10#5) 8 := by
      apply Vector.ext; intro i hi
      simp only [readWords, Vector.getElem_ofFn]
      exact rS _ (by bv_omega) (by bv_omega) (by bv_omega)
    have mS : readWords S.mem (s.getReg 10#5 + 128#32) 16 = readWords s.mem (s.getReg 10#5 + 128#32) 16 := by
      apply Vector.ext; intro i hi
      simp only [readWords, Vector.getElem_ofFn]
      exact rS _ (by bv_omega) (by bv_omega) (by bv_omega)
    have e12 : (readWords S.mem (s.getReg 10#5 + 32#32) 16)[12] =
        (read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5) ^^^ IV 4 := by
      simp only [readWords, Vector.getElem_ofFn]
      rw [show s.getReg 10#5 + 32#32 + BitVec.ofNat 32 (4 * 12) = s.getReg 10#5 + 80#32 by bv_omega, cut_mem,
        read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega), read_write_same4, ← cvdef_0]
      rfl
    have e14 : (readWords S.mem (s.getReg 10#5 + 32#32) 16)[14] =
        (if decide (s.getReg 12#5 = 1#32) = true then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 := by
      simp only [readWords, Vector.getElem_ofFn]
      rw [show s.getReg 10#5 + 32#32 + BitVec.ofNat 32 (4 * 14) = s.getReg 10#5 + 88#32 by bv_omega, cut_mem,
        read_write_same4]
      rcases hl with h | h <;> rw [h] <;> rfl
    have hc : read T.mem (s.getReg 10#5 + 192#32) 4 = read s.mem (s.getReg 10#5 + 192#32) 4 + s.getReg 11#5 := by
      rw [read_of_outside tm _ _ (by bv_omega), cut_mem,
        read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega),
        read_write_disjoint (h := by bv_omega) (ha := by bv_omega) (hc := by bv_omega), read_write_same4, cvdef_1]
    refine ⟨?_, hc⟩
    rw [th, if_pos rfl, compress_eq _ _ _ _ _ e12 e14, hS, mS]
  · have trr' : ∀ i, calleeSaved i → T.getReg i = S.getReg i := fun i hi =>
      trr i (by rintro rfl; simp [calleeSaved] at hi)
    rv_callee with trr'
    all_goals simp only [cut_r9, cut_r18, cut_r19, cut_r20, cut_r21, cut_r22, cut_r23, cut_r24, cut_r25, cut_r26,
      cut_r27]
  · intro a ha hb
    simp only [set_mem, jump_mem, next_mem]
    rw [tm a (by omega), cut_mem]
    repeat rw [write_outside (h := by bv_omega) (ha := by bv_omega)]

end RV
