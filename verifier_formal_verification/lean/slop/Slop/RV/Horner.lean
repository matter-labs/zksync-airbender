import Slop.RV.HornerLoop
import Slop.RV.HornerEpi

/-! `ext4_horner(out, coeffs, n, x)`: `out ← ∑_{i < n} cᵢ xⁱ` (`hornerPost`), for any implementation of `ext4_mul_add`
placed right after it (its only callee): the prologue (one block), then the `n = 0` path or the loop set-up (one
block) and the loop (`HornerLoop`), then the epilogue (`HornerEpi`, `horner_fin`). -/

namespace RV
open Spec RV.Sym RV.Block
set_option maxHeartbeats 400000

sym_run HPro := Code.ext4_horner.take 13
sym_run HSet := (Code.ext4_horner.drop 14).take 5

/-- Both paths from the epilogue (word 26) of `ext4_horner`, entered from `s`: the state `E` there holds the saved
registers in the frame, `out` in `s1`, and the sum in `acc` (at `sp₀ - 40`); memory outside the frame and the
registers `s5 … s11` are as at entry. -/
theorem horner_fin (A : Word) (s E : State) (FM : Nat) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 168 ≤ 4194304)
    (hcode : CodeAt E A Code.ext4_horner) (hpc : E.pc = A + 104#32)
    (h2 : E.getReg 2#5 = s.getReg 2#5 + 4294967248#32) (h9 : E.getReg 9#5 = s.getReg 10#5)
    (hsp : (s.getReg 2#5).toNat % 16 = 0) (hlo : 4194304 + 48 + FM ≤ (s.getReg 2#5).toNat)
    (hhi : (s.getReg 2#5).toNat ≤ 1073741824) (ho4 : (s.getReg 10#5).toNat % 4 = 0)
    (hos : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat) (hor : (s.getReg 10#5).toNat + 16 ≤ 1073741824)
    (hra : (s.getReg 1#5).toNat % 4 = 0)
    (h1 : read E.mem (s.getReg 2#5 + 4294967292#32) 4 = s.getReg 1#5)
    (h8 : read E.mem (s.getReg 2#5 + 4294967288#32) 4 = s.getReg 8#5)
    (h9' : read E.mem (s.getReg 2#5 + 4294967284#32) 4 = s.getReg 9#5)
    (h18 : read E.mem (s.getReg 2#5 + 4294967280#32) 4 = s.getReg 18#5)
    (h19 : read E.mem (s.getReg 2#5 + 4294967276#32) 4 = s.getReg 19#5)
    (h20 : read E.mem (s.getReg 2#5 + 4294967272#32) 4 = s.getReg 20#5)
    (hhiR : ∀ i : Reg, 21 ≤ i.toNat → i.toNat ≤ 27 → E.getReg i = s.getReg i)
    (hcA : canon4 E.mem (s.getReg 2#5 + 4294967256#32))
    (hAcc : e4At E.mem (s.getReg 2#5 + 4294967256#32) = ∑ i ∈ Finset.range (s.getReg 12#5).toNat,
      e4At s.mem (s.getReg 11#5 + BitVec.ofNat 32 (16 * i)) * e4At s.mem (s.getReg 13#5) ^ i)
    (hm : ∀ a : Word, a.toNat + (48 + FM) < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
      E.mem a = s.mem a) :
    ∃ m T, run m E = some T ∧ T.pc = s.getReg 1#5 ∧ hornerPost s T ∧
      (∀ i, calleeSaved i → T.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat + (48 + FM) < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 16 ≤ a.toNat → T.mem a = s.mem a) := by
  obtain ⟨m, T, hT, hpcT, t2, t8, t9, t18, t19, t20, thi, tcA, tA, tm⟩ := horner_epi A (s.getReg 2#5)
    (s.getReg 10#5) _ _ _ _ _ _ E hA hAr hcode hpc h2 h9 hsp (by omega) hhi ho4 hos hor hra h1 h8 h9' h18 h19 h20
  refine ⟨m, T, hT, hpcT, ⟨tcA hcA, by rw [tA, hAcc]⟩, calleeSaved_all _ t2 t8 t9 t18 t19 t20
    ?_ ?_ ?_ ?_ ?_ ?_ ?_, fun a ha hb => by rw [tm a hb, hm a ha]⟩
  all_goals exact (thi _ (by decide) (by decide)).trans (hhiR _ (by decide) (by decide))

/-- `ext4_horner` at any address `A`, with an `ext4_mul_add` implementation `codeM` (and its callees) at `A + 0xa8`. -/
theorem ext4_horner_impl (A : Word) (codeM : List Word) (calleesM : List (Word × List Word)) (FM : Nat)
    (hI : ImplementsAtW (A + 168#32) codeM calleesM FM mulAddPre 16 mulAddPost)
    (hAr : A.toNat + 168 + 4 * codeM.length ≤ 4194304)
    (hcal : ∀ c ∈ calleesM, c.1.toNat + 4 * c.2.length ≤ 4194304) :
    ImplementsAtW A Code.ext4_horner ((A + 168#32, codeM) :: calleesM) (48 + FM) hornerPre 16 hornerPost := by
  intro s hentry hcallees hcall hpre
  have hcM : CodeAt s (A + 168#32) codeM := hcallees _ List.mem_cons_self
  have hcal' : ∀ c ∈ calleesM, CodeAt s c.1 c.2 := fun c hc => hcallees c (List.mem_cons_of_mem _ hc)
  simp only [hornerPre, argOk, RAM_END] at hpre
  obtain ⟨⟨ho4, hos, hor⟩, ⟨hX4, hXs, hXr⟩, hcX, hT4, hTs, hTr, hC⟩ := hpre
  obtain ⟨hcode, hal, hromL, hra, hsp, hlo, hhi⟩ := hcall
  rw [hentry] at hcode hal hromL
  have hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  have hsp : (s.getReg 2#5).toNat % 16 = 0 := hsp
  have hlo : ROM_END + (48 + FM) ≤ (s.getReg 2#5).toNat := hlo
  replace hlo : 4194304 + 48 + FM ≤ (s.getReg 2#5).toNat := by simp only [ROM_END] at hlo; omega
  have hhi : (s.getReg 2#5).toNat ≤ 1073741824 := hhi
  have hL : Code.ext4_horner.length = 42 := rfl
  have hAr' : A.toNat + 168 ≤ 4194304 := by omega
  -- the prologue, words 0 … 12: the frame (6 saved registers), `acc = 0`, `s0`, `s1 = out`
  obtain ⟨S1, hrun1, hpc1, -, hrel1, hrom1, hout1, hfr1⟩ := block_at Code.ext4_horner 0 13 HPro.instrs HPro.σ s A
    [⟨2, -48, 0, 4⟩] [] HPro.dec HPro.run (by rw [hL]; omega) (by rw [hentry]; simp) hal hromL hcode (by sym_side)
    (by simp) (by decide +kernel)
  have mS1 : ∀ a : Word, a.toNat + 48 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
      S1.mem a = s.mem a := fun a ha =>
    out_frame hfr1 ⟨2, -48, 0, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; omega)
  have sv : ∀ (k : Word) (r : Nat), r < 32 → outOK HPro.σ [⟨2, -48, 0, 4⟩] [] 2 k = true →
      outNode HPro.σ 2 k = r → read S1.mem (s.getReg 2#5 + k) 4 = s.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by rw [hout1 2 k (by decide) hok, hn]; exact val_init HPro.instrs HPro.σ HPro.run s r hr
  have s1sp : S1.getReg 2#5 = s.getReg 2#5 + 4294967248#32 :=
    Rel.reg_addr HPro.instrs HPro.run hrel1 2#5 2 4294967248#32 (by decide) (by decide +kernel) (by decide +kernel)
  have s1o : S1.getReg 9#5 = s.getReg 10#5 :=
    Rel.reg_var HPro.instrs HPro.run hrel1 9#5 10 (by decide) (by decide +kernel)
  have s1r : ∀ r : Reg, (HPro.σ.reg r).val = r.toNat → S1.getReg r = s.getReg r := fun r h =>
    Rel.reg_same HPro.instrs HPro.run hrel1 r h
  have s1hi := regs_same_range HPro.instrs HPro.run hrel1 21 27 (by decide +kernel)
  have hcode1 : CodeAt S1 A Code.ext4_horner := codeAt_of_rom hcode hromL hrom1
  -- the saved registers and `acc`, in the frame
  have f1 := sv 4294967292#32 1 (by decide) (by decide +kernel) (by decide +kernel)
  have f8 := sv 4294967288#32 8 (by decide) (by decide +kernel) (by decide +kernel)
  have f9 := sv 4294967284#32 9 (by decide) (by decide +kernel) (by decide +kernel)
  have f18 := sv 4294967280#32 18 (by decide) (by decide +kernel) (by decide +kernel)
  have f19 := sv 4294967276#32 19 (by decide) (by decide +kernel) (by decide +kernel)
  have f20 := sv 4294967272#32 20 (by decide) (by decide +kernel) (by decide +kernel)
  have a0 := sv 4294967256#32 0 (by decide) (by decide +kernel) (by decide +kernel)
  have a4 := sv 4294967260#32 0 (by decide) (by decide +kernel) (by decide +kernel)
  have a8 := sv 4294967264#32 0 (by decide) (by decide +kernel) (by decide +kernel)
  have a12 := sv 4294967268#32 0 (by decide) (by decide +kernel) (by decide +kernel)
  have hacc : canon4 S1.mem (s.getReg 2#5 + 4294967256#32) ∧ e4At S1.mem (s.getReg 2#5 + 4294967256#32) = 0 := by
    simp only [canon4, e4At, BitVec.add_assoc, BitVec.reduceAdd, a0, a4, a8, a12, getReg_x0]
    exact ⟨by decide, e4_zero⟩
  rcases (by bv_omega : s.getReg 12#5 = 0#32 ∨ 1 ≤ (s.getReg 12#5).toNat) with hn | hn
  · -- `n = 0`: to the epilogue
    have hbr := run_branch_t hcode1 hal hromL (fun _ _ => rfl) 13 0x02060a63#32 (by decide +kernel) hpc1 .eq 12#5
      0#5 0x34#32 decode_ext4_horner_02060a63 (by rw [s1r 12#5 (by decide +kernel), hn]; simp [Cond.holds, getReg_x0]) 26 (by decide)
    obtain ⟨m, T, hT, hP⟩ := horner_fin A s (S1.setPC (A + BitVec.ofNat 32 (4 * 26))) FM hal hAr' hcode1 rfl s1sp s1o
      hsp hlo hhi ho4 hos hor hra f1 f8 f9 f18 f19 f20 s1hi hacc.1
      (hacc.2.trans (by rw [hn]; simp)) (fun a ha => mS1 a (by omega))
    exact ⟨_, T, run_trans hrun1 (run_trans hbr hT), hP⟩
  · -- `n ≥ 1`: the loop's set-up, words 14 … 18
    have hbf := run_branch_f hcode1 hal hromL (fun _ _ => rfl) 13 0x02060a63#32 (by decide +kernel) hpc1 .eq 12#5
      0#5 0x34#32 decode_ext4_horner_02060a63 (by
        rw [s1r 12#5 (by decide +kernel)]; simp only [Cond.holds, getReg_x0]
        exact decide_eq_false fun h => by rw [h] at hn; simp at hn)
    obtain ⟨S2, hrun2, hpc2, -, hrel2, hrom2, -, -⟩ := block_at Code.ext4_horner 14 5 HSet.instrs HSet.σ
      S1.nextInstr A [] [] HSet.dec HSet.run (by rw [hL]; omega) (by rw [next_pc, hpc1]; bv_omega) hal hromL
      (codeAt_of_rom hcode1 hromL fun _ _ => rfl) (by simp) (by simp) (by decide +kernel)
    have s2r : ∀ r : Reg, (HSet.σ.reg r).val = r.toNat → S2.getReg r = S1.getReg r := fun r h =>
      Rel.reg_same HSet.instrs HSet.run hrel2 r h
    have s2m : S2.mem = S1.mem := Rel.mem_nil hrel2 (by decide +kernel)
    have hU : ∀ a : Word, (s.getReg 2#5).toNat ≤ a.toNat → S2.mem a = s.mem a := fun a ha => by
      rw [s2m]; exact mS1 a (Or.inr ha)
    have hrS2 : ∀ b : Word, b.toNat < ROM_END → S2.mem b = s.mem b := fun b hb => by
      rw [s2m]; exact mS1 b (Or.inl (by simp only [ROM_END] at hb; omega))
    have hcU : ∀ p : Word, (s.getReg 2#5).toNat ≤ p.toNat → p.toNat + 16 ≤ 1073741824 → _ :=
      fun p hp1 hp2 => e4At_congr (m := s.mem) (m' := S2.mem) (p := p) (by omega) (fun a ha1 ha2 => hU a (by omega))
    have h20 : S2.getReg 20#5 = s.getReg 11#5 + BitVec.ofNat 32 (16 * ((s.getReg 12#5).toNat - 1)) := by
      rw [(hrel2.2.2.1 20#5).2]
      sym_unfold
      simp only [alu, ctxOf, next_r, s1r 11#5 (by decide +kernel), s1r 12#5 (by decide +kernel)]
      rw [show (BitVec.setWidth 5 4#32).toNat = 4 from rfl, BitVec.shiftLeft_eq_mul_twoPow]
      bv_omega
    obtain ⟨m3, S3, hrun3, hpc3, h23, hcA3, hA3, hcs3, hm3⟩ := horner_loop A (s.getReg 11#5) (s.getReg 13#5)
      (s.getReg 2#5) codeM calleesM FM hI hal hAr hcal
      (fun i => e4At s.mem (s.getReg 11#5 + BitVec.ofNat 32 (16 * i))) (e4At s.mem (s.getReg 13#5))
      (s.getReg 12#5).toNat hsp hlo hhi hX4 hXs hXr hT4 hTs hTr (s.getReg 12#5).toNat S2 hn le_rfl
      (codeAt_of_rom hcode hromL hrS2)
      (codeAt_of_rom hcM (by simp only [ROM_END]; bv_omega) hrS2)
      (fun c hc => codeAt_of_rom (hcal' c hc) (by simp only [ROM_END]; exact hcal c hc) hrS2)
      (by rw [hpc2]) (by rw [s2r 2#5 (by decide +kernel), s1sp])
      (by rw [Rel.reg_var HSet.instrs HSet.run hrel2 18#5 13 (by decide) (by decide +kernel), next_r,
        s1r 13#5 (by decide +kernel)])
      (by rw [Rel.reg_var HSet.instrs HSet.run hrel2 19#5 12 (by decide) (by decide +kernel), next_r,
        s1r 12#5 (by decide +kernel)]; simp) h20
      ((hcU _ hXs hXr).2.mpr hcX) (hcU _ hXs hXr).1
      (fun i hi => ⟨(hcU _ (by bv_omega) (by bv_omega)).2.mpr (hC i hi), (hcU _ (by bv_omega) (by bv_omega)).1⟩)
      (by rw [s2m]; exact hacc.1) (by rw [s2m, Nat.sub_self, hacc.2]; rfl)
    -- the frame is below `sp₀ - 24`'s reach of the loop: still the prologue's
    have fr : ∀ k : Word, 4294967272 ≤ k.toNat → k.toNat ≤ 4294967292 →
        read S3.mem (s.getReg 2#5 + k) 4 = read S1.mem (s.getReg 2#5 + k) 4 := fun k hk1 hk2 => by
      rw [← s2m]; apply read_congr; intro j hj; apply hm3; right; bv_omega
    have hfin := horner_fin A s S3 FM hal hAr' (codeAt_of_rom hcode hromL fun b hb => by
        rw [hm3 b (by left; simp only [ROM_END] at hb; omega)]; exact hrS2 b hb)
      hpc3 h23 (by rw [hcs3 9#5 (by rv_callee_saved) (by decide) (by decide), s2r 9#5 (by decide +kernel), s1o])
      hsp hlo hhi ho4 hos hor hra
      ((fr _ (by decide) (by decide)).trans f1) ((fr _ (by decide) (by decide)).trans f8)
      ((fr _ (by decide) (by decide)).trans f9) ((fr _ (by decide) (by decide)).trans f18)
      ((fr _ (by decide) (by decide)).trans f19) ((fr _ (by decide) (by decide)).trans f20)
      (fun i h1 h2 => by
        rw [hcs3 i (by unfold calleeSaved; bv_omega) (by bv_omega) (by bv_omega),
          RV.Block.regs_same_range HSet.instrs HSet.run hrel2 21 27 (by decide +kernel) i h1 h2, next_r]
        exact s1hi i h1 h2)
      hcA3 (by rw [hA3, hornerAcc_full])
      (fun a ha => by rw [hm3 a (by omega), s2m]; exact mS1 a (by omega))
    obtain ⟨m, T, hT, hP⟩ := hfin
    exact ⟨_, T, run_trans hrun1 (run_trans hbf (run_trans hrun2 (run_trans hrun3 hT))), hP⟩
end RV
