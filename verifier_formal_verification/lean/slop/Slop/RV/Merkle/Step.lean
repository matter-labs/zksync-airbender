import Slop.RV.CallW
import Slop.RV.CopyRun
import Slop.RV.Merkle.Block
import Slop.RV.Merkle.Contract
import Slop.RV.Merkle.StepRuns
import Slop.Block.Block

/-! `merkle_step(st, right, sib)`: one level of a Merkle path, the node in `st.state` and the sibling at `sib` into
the parent (`Spec.hash2`): the side branch (by steps), the block (`merkle_block`), a tail call of
`blake2s_compress`. -/

namespace RV
open _root_.RV.Sym Spec
set_option maxHeartbeats 400000

theorem setReg0_getReg (T : State) (v : Word) (r : Reg) : (T.setReg 0#5 v).getReg r = T.getReg r := by
  unfold State.getReg State.setReg
  by_cases h : r = 0
  · simp [h]
  · have h' : ¬ r = 0#5 := h
    simp only [h, h', ite_false]

theorem setPC_getReg' (T : State) (t : Word) (r : Reg) : (T.setPC t).getReg r = T.getReg r := rfl
theorem setPC_setReg_mem (T : State) (t v : Word) (r : Reg) : ((T.setPC t).setReg r v).mem = T.mem := rfl

/-- From word 9 (the halves' pointers `L`, `R` in `a1`, `a2`): the block, the tail call, the return to `s`'s `ra`
with the hash of the halves at `a0`. -/
theorem merkle_from9 (A : Word) (s S : State) (L R : Word)
    (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * 72 ≤ ROM_END)
    (hAbr : (A + 284#32 + 0xFFFFDB7C#32).toNat + 4 * Code.blake2s_compress.length ≤ ROM_END)
    (hcode : CodeAt S A Code.merkle_step) (hbl : CodeAt S (A + 284#32 + 0xFFFFDB7C#32) Code.blake2s_compress)
    (hpc : S.pc = A + 36#32) (h2 : S.getReg 2#5 = s.getReg 2#5 + 4294967280#32) (h10 : S.getReg 10#5 = s.getReg 10#5)
    (h11 : S.getReg 11#5 = L) (h12 : S.getReg 12#5 = R)
    (hra : read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5) (hs0 : read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5)
    (hcs : ∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r)
    (hmem : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S.mem a = s.mem a)
    (hra4 : (s.getReg 1#5).toNat % 4 = 0) (hsp : (s.getReg 2#5).toNat % 16 = 0)
    (hsp1 : ROM_END + 160 ≤ (s.getReg 2#5).toNat)
    (ha4 : (s.getReg 10#5).toNat % 4 = 0) (hspa : (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat)
    (hR : (s.getReg 10#5).toNat + 132 ≤ RAM_END)
    (hL4 : L.toNat % 4 = 0) (hL1 : (s.getReg 2#5).toNat ≤ L.toNat) (hL2 : L.toNat + 32 ≤ RAM_END)
    (hR4 : R.toNat % 4 = 0) (hR1 : (s.getReg 2#5).toNat ≤ R.toNat) (hR2 : R.toNat + 32 ≤ RAM_END)
    (hRd : R.toNat + 32 ≤ (s.getReg 10#5).toNat + 64 ∨ (s.getReg 10#5).toNat + 96 ≤ R.toNat) :
    ∃ m t, run m S = some t ∧ t.pc = s.getReg 1#5 ∧
      readWords t.mem (s.getReg 10#5) 8 = hash2 (readWords s.mem L 8) (readWords s.mem R 8) ∧
      (∀ i, calleeSaved i → t.getReg i = s.getReg i) ∧
      (∀ a : Word, a.toNat + 160 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat →
        a.toNat < (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + 132 ≤ a.toNat → t.mem a = s.mem a) := by
  simp only [ROM_END, RAM_END] at *
  have hspn : (S.getReg 2#5).toNat = (s.getReg 2#5).toNat - 16 := by rw [h2]; bv_omega
  obtain ⟨S', hrun, hpc', r10, r11, r12, r1, r8, r2, rcs, hiv, hblk, hct, hfr, hromB⟩ :=
    merkle_block S A hal (by simp only [ROM_END]; rw [show Code.merkle_step.length = 72 from rfl]; omega) hcode hpc
      (by omega) (by simp only [ROM_END]; omega) (by rw [h10]; exact ha4) (by rw [h10]; omega)
      (by rw [h10]; simp only [RAM_END]; omega) (by rw [h11]; exact hL4) (by rw [h11]; simp only [ROM_END]; omega)
      (by rw [h11]; simp only [RAM_END]; omega) (by rw [h12]; exact hR4) (by rw [h12]; simp only [ROM_END]; omega)
      (by rw [h12]; simp only [RAM_END]; omega) (by rw [h10, h12]; omega)
  -- the tail call `jal x0, blake2s_compress`
  set Ab := A + 284#32 + 0xFFFFDB7C#32 with hAb
  have hfetch : read S'.mem S'.pc 4 = 0xb7dfd06f#32 := by
    rw [hpc', read_congr S'.mem S.mem _ 4 (fun j hj => hromB _ (by simp only [ROM_END]; bv_omega))]
    have hw : ∀ h : 71 < Code.merkle_step.length, Code.merkle_step[71]'h = 0xb7dfd06f#32 := by decide +kernel
    exact (hcode 71 (by rw [show Code.merkle_step.length = 72 from rfl]; omega)).trans (hw _)
  have hstep : step S' = some ((S'.setPC Ab).setReg 0#5 (S'.pc + 4)) := by
    rw [step_fetch S' _ (by rw [hpc']; bv_omega) (by rw [hpc']; simp only [ROM_END]; bv_omega) hfetch,
      show decode 0xb7dfd06f#32 = some (.jal 0#5 0xFFFFDB7C#32) by decide +kernel, Option.bind_some,
      exec_jal _ _ _ (by rw [hpc']; simp only [hAb] at hAbr ⊢; bv_omega), hpc']
  obtain ⟨X, hX⟩ : ∃ X, X = (S'.setPC Ab).setReg 0#5 (S'.pc + 4) := ⟨_, rfl⟩
  rw [← hX] at hstep
  have xr : ∀ r : Reg, X.getReg r = S'.getReg r := fun r => by rw [hX, setReg0_getReg, setPC_getReg']
  have xm : X.mem = S'.mem := by rw [hX, setPC_setReg_mem]
  have xsp : X.getReg 2#5 = s.getReg 2#5 := by rw [xr, r2, h2]; bv_omega
  have xrom : ∀ b : Word, b.toNat < ROM_END → X.mem b = S.mem b := fun b hb => by rw [xm, hromB b hb]
  have xpc : X.pc = Ab := by rw [hX]; rfl
  obtain ⟨n, U, hrunU, hpcU, hpost, hcsU, hmemU⟩ := blake2s_compress_impl Ab X xpc (by simp)
    ⟨by rw [xpc]; exact codeAt_of_rom hbl hAbr xrom,
      by rw [xpc]; simp only [hAb]; bv_omega,
      by rw [xpc]; simp only [ROM_END]; omega,
      by show (X.getReg 1#5).toNat % 4 = 0; rw [xr, r1, hra]; exact hra4,
      by show (X.getReg 2#5).toNat % 16 = 0; rw [xsp]; exact hsp,
      by show ROM_END + 160 ≤ (X.getReg 2#5).toNat; rw [xsp]; simp only [ROM_END]; omega,
      by show (X.getReg 2#5).toNat ≤ RAM_END; rw [xsp]; simp only [RAM_END]; omega⟩
    (by simp only [blakePre, xsp, xr, r10, r12, h10, RAM_END]; exact ⟨ha4, hspa, hR, Or.inr trivial⟩)
  replace hcsU : ∀ i, calleeSaved i → U.getReg i = X.getReg i := hcsU
  replace hmemU : ∀ a : Word, a.toNat + 160 < (X.getReg 2#5).toNat ∨ (X.getReg 2#5).toNat ≤ a.toNat →
      a.toNat < (X.getReg 10#5).toNat ∨ (X.getReg 10#5).toNat + 132 ≤ a.toNat → U.mem a = X.mem a := hmemU
  simp only [blakePost, xr, r10, r11, r12, h10] at hpost
  -- the halves, read where `merkle_check` put them: untouched by the prologue's two stack words
  have hhalf : ∀ P : Word, (s.getReg 2#5).toNat ≤ P.toNat → P.toNat + 32 ≤ 1073741824 →
      wordsAt S.mem P 8 = readWords s.mem P 8 := fun P h1 h2' => by
    apply Vector.ext; intro i hi
    simp only [wordsAt, readWords, Vector.getElem_ofFn]
    exact read_congr _ _ _ _ (fun j hj => hmem _ (by right; bv_omega))
  refine ⟨_, U, run_trans (run_trans hrun (show run 1 S' = some X by rw [run_succ, hstep]; rfl)) hrunU, ?_, ?_, fun i hi => ?_,
    fun a ha hb => ?_⟩
  · rw [hpcU]; show X.getReg 1#5 = _; rw [xr, r1, hra]
  · show wordsAt U.mem (s.getReg 10#5) 8 = _
    rw [hpost.1, xm, ← h10, hiv, hblk, hct, h11, h12, hhalf L hL1 hL2, hhalf R hR1 hR2]
    rfl
  · rw [hcsU i hi, xr]
    by_cases i2 : i = 2#5
    · subst i2; rw [r2, h2]; bv_omega
    by_cases i8 : i = 8#5
    · subst i8; rw [r8, hs0]
    rw [rcs i hi i2 i8, hcs i hi i2 i8]
  · rw [hmemU a (by rw [xsp]; exact ha) (by rw [xr, r10, h10]; exact hb), xm,
      hfr a (by rw [h10]; exact hb), hmem a (by omega)]

theorem take_drop_of_take {C D : List Word} {k : Nat} (h : C.take k = D.take k) (i n : Nat) (hn : i + n ≤ k) :
    (C.drop i).take n = (D.drop i).take n := by
  have e := congrArg (fun l => (l.drop i).take n) h
  simp only [List.drop_take, List.take_take] at e
  rwa [Nat.min_eq_left (by omega)] at e

theorem getElem?_of_take {C D : List Word} {k : Nat} (h : C.take k = D.take k) (i : Nat) (hi : i < k) :
    C[i]? = D[i]? := by
  have e := congrArg (·[i]?) h
  simpa only [List.getElem?_take, hi, ite_true] using e

/-- Words 0 … 8 of `merkle_step`, in any code `C` that starts with them (the delegation build's does): the frame
(`ra`, `s0` saved below `sp`, `sp` down 16), then the halves' pointers by the side word `a1`: the node `a0` left
and the sibling `a2` right if `a1 = 0`, the other way round otherwise. -/
theorem merkle_side (C : List Word) (hC : C.take 9 = Code.merkle_step.take 9) (hCl : 9 ≤ C.length) (s : State)
    (A : Word) (hpc : s.pc = A) (hal : A.toNat % 4 = 0) (hrom : A.toNat + 4 * C.length ≤ ROM_END)
    (hcode : CodeAt s A C) (hsp1 : ROM_END + 8 ≤ (s.getReg 2#5).toNat) (hsp2 : (s.getReg 2#5).toNat ≤ RAM_END)
    (hsp : (s.getReg 2#5).toNat % 4 = 0) :
    ∃ m S, run m s = some S ∧ S.pc = A + 36#32 ∧ S.getReg 2#5 = s.getReg 2#5 + 4294967280#32 ∧
      S.getReg 10#5 = s.getReg 10#5 ∧
      S.getReg 11#5 = (if s.getReg 11#5 = 0 then s.getReg 10#5 else s.getReg 12#5) ∧
      S.getReg 12#5 = (if s.getReg 11#5 = 0 then s.getReg 12#5 else s.getReg 10#5) ∧
      read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5 ∧ read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5 ∧
      (∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r) ∧
      (∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S.mem a = s.mem a) ∧
      (∀ b : Word, b.toNat < ROM_END → S.mem b = s.mem b) := by
  have hsp1' := hsp1
  have hsp2' := hsp2
  simp only [ROM_END, RAM_END] at hsp1' hsp2'
  -- the frame, words 0 … 3
  obtain ⟨S1, hrun1, hpc1, -, hrel1, hrom1, hout1, hfr1⟩ := block_at C 0 4 MSPro.instrs MSPro.σ s A [⟨2, -8, 0, 4⟩]
    [] (by rw [take_drop_of_take hC 0 4 (by decide)]; exact MSPro.dec) MSPro.run (by omega) (by rw [hpc]; simp) hal
    hrom hcode (by sym_side) (by simp) (by decide +kernel)
  have m1 : ∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S1.mem a = s.mem a :=
    fun a ha => out_frame hfr1 ⟨2, -8, 0, 1⟩ (by decide +kernel) (by decide) (by sym_side) a
      (by simp only [Region.Outside]; omega)
  have sv : ∀ (k : Word) (r : Nat), r < 32 → outOK MSPro.σ [⟨2, -8, 0, 4⟩] [] 2 k = true →
      outNode MSPro.σ 2 k = r → read S1.mem (s.getReg 2#5 + k) 4 = s.getReg (BitVec.ofNat 5 r) :=
    fun k r hr hok hn => by rw [hout1 2 k (by decide) hok, hn]; exact val_init MSPro.instrs MSPro.σ MSPro.run s r hr
  have s1sp : S1.getReg 2#5 = s.getReg 2#5 + 4294967280#32 :=
    Rel.reg_addr MSPro.instrs MSPro.run hrel1 2#5 2 _ (by decide) (by decide +kernel) (by decide +kernel)
  have s1r : ∀ r : Reg, (MSPro.σ.reg r).val = r.toNat → S1.getReg r = s.getReg r := fun r h =>
    Rel.reg_same MSPro.instrs MSPro.run hrel1 r h
  have hra : read S1.mem (S1.getReg 2#5 + 12#32) 4 = s.getReg 1#5 := by
    rw [s1sp, show s.getReg 2#5 + 4294967280#32 + 12#32 = s.getReg 2#5 + 4294967292#32 by bv_omega]
    exact sv _ 1 (by decide) (by decide +kernel) (by decide +kernel)
  have hs0 : read S1.mem (S1.getReg 2#5 + 8#32) 4 = s.getReg 8#5 := by
    rw [s1sp, show s.getReg 2#5 + 4294967280#32 + 8#32 = s.getReg 2#5 + 4294967288#32 by bv_omega]
    exact sv _ 8 (by decide) (by decide +kernel) (by decide +kernel)
  have hw4 : C[4]? = some 0x00058863#32 := by rw [getElem?_of_take hC 4 (by decide)]; rfl
  -- a state at word 9 with `S1`'s memory and registers but `a1`, `a2`
  have fin : ∀ (m : Nat) (S : State), run m S1 = some S → S.pc = A + 36#32 → S.mem = S1.mem →
      (∀ r : Reg, r ≠ 11#5 → r ≠ 12#5 → S.getReg r = S1.getReg r) →
      S.getReg 11#5 = (if s.getReg 11#5 = 0 then s.getReg 10#5 else s.getReg 12#5) →
      S.getReg 12#5 = (if s.getReg 11#5 = 0 then s.getReg 12#5 else s.getReg 10#5) →
      ∃ m S, run m s = some S ∧ S.pc = A + 36#32 ∧ S.getReg 2#5 = s.getReg 2#5 + 4294967280#32 ∧
        S.getReg 10#5 = s.getReg 10#5 ∧
        S.getReg 11#5 = (if s.getReg 11#5 = 0 then s.getReg 10#5 else s.getReg 12#5) ∧
        S.getReg 12#5 = (if s.getReg 11#5 = 0 then s.getReg 12#5 else s.getReg 10#5) ∧
        read S.mem (S.getReg 2#5 + 12#32) 4 = s.getReg 1#5 ∧ read S.mem (S.getReg 2#5 + 8#32) 4 = s.getReg 8#5 ∧
        (∀ r : Reg, calleeSaved r → r ≠ 2#5 → r ≠ 8#5 → S.getReg r = s.getReg r) ∧
        (∀ a : Word, a.toNat + 8 < (s.getReg 2#5).toNat ∨ (s.getReg 2#5).toNat ≤ a.toNat → S.mem a = s.mem a) ∧
        (∀ b : Word, b.toNat < ROM_END → S.mem b = s.mem b) := by
    intro m S hrun hpcS hm hr h11 h12
    have h2 : S.getReg 2#5 = S1.getReg 2#5 := hr _ (by decide) (by decide)
    refine ⟨4 + m, S, run_trans hrun1 hrun, hpcS, h2.trans s1sp, (hr _ (by decide) (by decide)).trans
      (s1r _ (by decide +kernel)), h11, h12, by rw [hm, h2]; exact hra, by rw [hm, h2]; exact hs0,
      fun r hr' h2' h8' => ?_, fun a ha => by rw [hm]; exact m1 a ha, fun b hb => by rw [hm]; exact hrom1 b hb⟩
    rcases calleeSaved_cases r hr' with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
      first | exact absurd rfl h2' | exact absurd rfl h8' |
        exact (hr _ (by decide) (by decide)).trans (s1r _ (by decide +kernel))
  by_cases h0 : s.getReg 11#5 = 0
  · -- word 4 taken: word 8, `a1 = a0`
    have hbt := run_branch_t hcode hal hrom hrom1 4 _ hw4 hpc1 .eq 11#5 0#5 16#32 rfl
      (by rw [s1r _ (by decide +kernel), h0, r_zero5]; decide) 8 (by decide)
    have hc2 : CodeAt (S1.setPC (A + BitVec.ofNat 32 (4 * 8))) A C := codeAt_of_rom hcode hrom hrom1
    obtain ⟨S2, hrun2, hpc2, -, hrel2, -, -, -⟩ := block_at C 8 1 MSLeft.instrs MSLeft.σ _ A [] []
      (by rw [take_drop_of_take hC 8 1 (by decide)]; exact MSLeft.dec) MSLeft.run (by omega) rfl hal hrom hc2
      (by simp) (by simp) (by decide +kernel)
    refine fin _ S2 (run_trans hbt hrun2) (by rw [hpc2]) (Rel.mem_nil hrel2 (by decide +kernel))
      (fun r h11 h12 => ?_) ?_ ?_
    · rw [Rel.reg_same MSLeft.instrs MSLeft.run hrel2 r (by
        revert h11 h12; generalize r = r; revert r; decide +kernel)]; rfl
    · simp only [h0, ↓reduceIte]
      rw [Rel.reg_var MSLeft.instrs MSLeft.run hrel2 11#5 10 (by decide) (by decide +kernel)]
      exact s1r _ (by decide +kernel)
    · simp only [h0, ↓reduceIte]
      rw [Rel.reg_same MSLeft.instrs MSLeft.run hrel2 12#5 (by decide +kernel)]
      exact s1r _ (by decide +kernel)
  · -- word 4 not taken: words 5, 6 swap the halves, word 7 jumps to word 9
    have hbf := run_branch_f hcode hal hrom hrom1 4 _ hw4 hpc1 .eq 11#5 0#5 16#32 rfl
      (by rw [s1r _ (by decide +kernel), r_zero5]; simpa [Cond.holds] using h0)
    have hc2 : CodeAt S1.nextInstr A C := codeAt_of_rom hcode hrom hrom1
    obtain ⟨S2, hrun2, hpc2, -, hrel2, hrom2, -, -⟩ := block_at C 5 2 MSSwap.instrs MSSwap.σ _ A [] []
      (by rw [take_drop_of_take hC 5 2 (by decide)]; exact MSSwap.dec) MSSwap.run (by omega)
      (by rw [next_pc, hpc1]; bv_omega) hal hrom hc2 (by simp) (by simp) (by decide +kernel)
    have hjal := run_jal hc2 hal hrom hrom2 7 0x0080006f#32 (by rw [getElem?_of_take hC 7 (by decide)]; rfl) hpc2
      0#5 8#32 rfl (A + 36#32) (by bv_omega) (by bv_omega)
    have m2 : S2.mem = S1.mem := Rel.mem_nil hrel2 (by decide +kernel)
    refine fin _ _ (run_trans hbf (run_trans hrun2 hjal)) (x0_pc _ _ _) m2 (fun r h11 h12 => ?_) ?_ ?_
    · rw [x0_getReg, Rel.reg_same MSSwap.instrs MSSwap.run hrel2 r (by
        revert h11 h12; generalize r = r; revert r; decide +kernel)]; rfl
    · simp only [h0, ↓reduceIte]
      rw [x0_getReg, Rel.reg_var MSSwap.instrs MSSwap.run hrel2 11#5 12 (by decide)
        (by decide +kernel), next_r]
      exact s1r _ (by decide +kernel)
    · simp only [h0, ↓reduceIte]
      rw [x0_getReg, Rel.reg_var MSSwap.instrs MSSwap.run hrel2 12#5 10 (by decide)
        (by decide +kernel), next_r]
      exact s1r _ (by decide +kernel)

theorem merkle_step_impl (A : Word)
    (hAbr : (A + 284#32 + 0xFFFFDB7C#32).toNat + 4 * Code.blake2s_compress.length ≤ ROM_END) :
    ImplementsAtW A Code.merkle_step [(A + 284#32 + 0xFFFFDB7C#32, Code.blake2s_compress)] 160 (merklePre 4 132) 132
      merklePost := by
  intro s hentry hcal ⟨hcode, hal, hrom, hra, hsp, hlo, hhi⟩ ⟨ha4, hspa, hR, hs4, hs1, hs2, hsd⟩
  rw [hentry] at hcode hal hrom
  replace hra : (s.getReg 1#5).toNat % 4 = 0 := hra
  replace hsp : (s.getReg 2#5).toNat % 16 = 0 := hsp
  replace hlo : ROM_END + 160 ≤ (s.getReg 2#5).toNat := hlo
  replace hhi : (s.getReg 2#5).toNat ≤ RAM_END := hhi
  have hL : Code.merkle_step.length = 72 := rfl
  simp only [ROM_END, RAM_END] at hR hs2 hlo hhi
  obtain ⟨m1, S, hrun, hpc, h2, h10, h11, h12, hra', hs0', hcs', hmem, srom⟩ := merkle_side Code.merkle_step rfl
    (by rw [hL]; omega) s A hentry hal hrom hcode (by simp only [ROM_END]; omega) (by simp only [RAM_END]; omega)
    (by omega)
  have hcS := codeAt_of_rom hcode hrom srom
  have hbS := codeAt_of_rom (hcal _ List.mem_cons_self) hAbr srom
  have hrom9 : A.toNat + 4 * 72 ≤ ROM_END := by rw [← hL]; exact hrom
  by_cases hr : s.getReg 11#5 = 0
  · simp only [hr, ↓reduceIte] at h11 h12
    obtain ⟨m, t, hrun', hpct, hpost, hcst, hfrt⟩ := merkle_from9 A s S (s.getReg 10#5) (s.getReg 12#5) hal hrom9
      hAbr hcS hbS hpc h2 h10 h11 h12 hra' hs0' hcs' hmem hra hsp (by simp only [ROM_END]; omega) ha4 hspa
      (by simp only [RAM_END]; omega) ha4 hspa (by simp only [RAM_END]; omega) hs4 hs1 (by simp only [RAM_END]; omega)
      (by omega)
    exact ⟨m1 + m, t, run_trans hrun hrun', hpct, by
      simp only [merklePost, hr, ne_eq, not_true_eq_false, ite_false]; exact hpost, hcst, hfrt⟩
  · simp only [hr, ↓reduceIte] at h11 h12
    obtain ⟨m, t, hrun', hpct, hpost, hcst, hfrt⟩ := merkle_from9 A s S (s.getReg 12#5) (s.getReg 10#5) hal hrom9
      hAbr hcS hbS hpc h2 h10 h11 h12 hra' hs0' hcs' hmem hra hsp (by simp only [ROM_END]; omega) ha4 hspa
      (by simp only [RAM_END]; omega) hs4 hs1 (by simp only [RAM_END]; omega) ha4 hspa (by simp only [RAM_END]; omega)
      (by omega)
    exact ⟨m1 + m, t, run_trans hrun hrun', hpct, by
      simp only [merklePost, hr, ne_eq, not_false_eq_true, ite_true]; exact hpost, hcst, hfrt⟩

end RV
