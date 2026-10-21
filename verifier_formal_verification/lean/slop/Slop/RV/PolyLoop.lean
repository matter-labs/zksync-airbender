import Slop.RV.MulMod
import Slop.RV.Code.poly_eval
import Slop.Block.Block
import Slop.Sym.Func

/-! The Horner loop of `poly_eval` (loop head at `poly_eval + 0x3c`): one iteration, then induction on the
remaining count. Generic in the code's address and in the coefficient table. The straight-line parts of an
iteration (`addi`s and the `jal`s) and of the exit are symbolic blocks (`sym_run`); the calls are `run_callAt`/`run_call`. -/

namespace RV
open RV.Sym RV.Block
set_option maxHeartbeats 400000

/-- Horner value of a coefficient list, `c₀` first: `c₀ + x (c₁ + x (c₂ + …))`. -/
def polyW (c : List Word) (x : Nat) : Nat := c.foldr (fun a acc => a.toNat + x * acc) 0

theorem polyW_drop (C : List Word) (x j : Nat) (h : j < C.length) :
    polyW (C.drop j) x = C[j].toNat + x * polyW (C.drop (j + 1)) x := by
  rw [List.drop_eq_getElem_cons h]; rfl

/-- One Horner step, modulo `P`. -/
theorem horner_step (s1 s2 acc x c W : Nat) (h2 : s2 % P = (s1 + c) % P) (h1 : s1 % P = (acc * x) % P)
    (h0 : acc % P = W % P) : s2 % P = (c + x * W) % P := by
  have hm : (acc * x) % P = (W * x) % P := by rw [Nat.mul_mod, h0, ← Nat.mul_mod]
  rw [h2, Nat.add_mod, h1, hm, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]

theorem reg_20_27 (i : Reg) (h1 : 20 ≤ i.toNat) (h2 : i.toNat ≤ 27) :
    i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5 := by
  bv_omega

sym_run PL1 := (Code.poly_eval.drop 15).take 2
sym_run PL2 := (Code.poly_eval.drop 20).take 1
sym_run PL3 := (Code.poly_eval.drop 24).take 6

namespace PolyR
abbrev rS : Region := ⟨2, 0, 32, 4⟩
end PolyR
open PolyR

/-- The exit of `poly_loop`: `j` to the epilogue (word 22), the epilogue block (words 24–29: restores `ra`, `s0`,
`s1`, `s2`, `s3`, `sp`) and `ret`. -/
theorem poly_epi (A : Word) (S : State) (sp0 ra0 v8 v9 v18 v19 : Word) (hA4 : A.toNat % 4 = 0)
    (hAr : A.toNat + 124 ≤ 4194304) (hcode : CodeAt S A Code.poly_eval) (hpc : S.pc = A + 88#32)
    (h2 : S.getReg 2#5 = sp0 + 4294967264#32) (hsp : sp0.toNat % 16 = 0) (hlo : 4194304 + 48 ≤ sp0.toNat)
    (hhi : sp0.toNat ≤ 1073741824) (hra : ra0.toNat % 4 = 0)
    (h1 : read S.mem (sp0 + 4294967292#32) 4 = ra0) (h8 : read S.mem (sp0 + 4294967288#32) 4 = v8)
    (h9 : read S.mem (sp0 + 4294967284#32) 4 = v9) (h18 : read S.mem (sp0 + 4294967280#32) 4 = v18)
    (h19 : read S.mem (sp0 + 4294967276#32) 4 = v19) :
    ∃ m S', run m S = some S' ∧ S'.pc = ra0 ∧ S'.getReg 2#5 = sp0 ∧ S'.getReg 8#5 = v8 ∧ S'.getReg 9#5 = v9 ∧
      S'.getReg 18#5 = v18 ∧ S'.getReg 19#5 = v19 ∧ S'.mem = S.mem ∧ S'.getReg 10#5 = S.getReg 10#5 ∧
      (∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → S'.getReg i = S.getReg i) := by
  obtain ⟨S4, hrun1, hpc4, hS4r, hS4m⟩ : ∃ S4, run 1 S = some S4 ∧ S4.pc = A + 96#32 ∧
      (∀ r : Reg, S4.getReg r = S.getReg r) ∧ S4.mem = S.mem :=
    ⟨_, run_jal hcode hA4 (by rw [show Code.poly_eval.length = 31 from rfl]; simp only [ROM_END]; omega)
      (fun _ _ => rfl) 22 0x0080006f#32 (by decide +kernel) (by rw [hpc]; try rfl) 0#5 8#32
      decode_poly_eval_0080006f (A + 96#32) (by bv_omega) (by bv_omega), by rw [x0_pc], fun r => x0_getReg S _ _ r, rfl⟩
  have h2S4 : S4.getReg 2#5 = sp0 + 4294967264#32 := by rw [hS4r, h2]
  -- a stack slot: `S4`'s `sp + k` is `sp0 + c`
  have fr : ∀ k c : Word, 4294967264#32 + k = c → read S.mem (S4.getReg 2#5 + k) 4 = read S.mem (sp0 + c) 4 :=
    fun k c hk => by rw [h2S4, BitVec.add_assoc, hk]
  have hcS4 : CodeAt S4 A Code.poly_eval := codeAt_mem_eq hS4m hcode
  have hR : ∀ R ∈ [PolyR.rS], R.b < 32 ∧ R.Holds (ctxOf S4) initPool := by
    have h2n : (S4.getReg 2#5).toNat = sp0.toNat - 32 := by rw [h2S4]; bv_omega
    simp (disch := decide) only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true, RV.Sym.Region.Holds, RV.Sym.initPool_val, RV.ROM_END, RV.RAM_END, PolyR.rS]
    omega
  obtain ⟨T, hrunT, hpcT, hrelT, hromT, -, hfrT⟩ := block_ret 24 6 PL3.instrs PL3.σ [PolyR.rS] []
    PL3.dec PL3.run (by decide) (by rw [hpc4]; try rfl) (by bv_omega)
    (by rw [show Code.poly_eval.length = 31 from rfl]; simp only [ROM_END]; bv_omega) hcS4 (by decide +kernel)
    hR (by simp) (by decide +kernel)
    (fun S' hrel => by
      rw [Rel.reg_load PL3.instrs PL3.run hrel 1#5 2 28#32 (by decide) (by decide +kernel) (by decide +kernel), hS4m, fr 28#32 4294967292#32 (by decide), h1]
      exact hra)
  have e1 : T.getReg 1#5 = ra0 := by
    rw [Rel.reg_load PL3.instrs PL3.run hrelT 1#5 2 28#32 (by decide) (by decide +kernel) (by decide +kernel),
      hS4m, fr 28#32 4294967292#32 (by decide), h1]
  refine ⟨_, T, run_trans hrun1 hrunT, by rw [hpcT, e1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrelT.reg_addr PL3.instrs PL3.run 2#5 2 32#32 (by decide) (by decide +kernel) (by decide +kernel), h2S4]
    bv_omega
  · rw [Rel.reg_load PL3.instrs PL3.run hrelT 8#5 2 24#32 (by decide) (by decide +kernel) (by decide +kernel),
      hS4m, fr 24#32 4294967288#32 (by decide), h8]
  · rw [Rel.reg_load PL3.instrs PL3.run hrelT 9#5 2 20#32 (by decide) (by decide +kernel) (by decide +kernel),
      hS4m, fr 20#32 4294967284#32 (by decide), h9]
  · rw [Rel.reg_load PL3.instrs PL3.run hrelT 18#5 2 16#32 (by decide) (by decide +kernel) (by decide +kernel),
      hS4m, fr 16#32 4294967280#32 (by decide), h18]
  · rw [Rel.reg_load PL3.instrs PL3.run hrelT 19#5 2 12#32 (by decide) (by decide +kernel) (by decide +kernel),
      hS4m, fr 12#32 4294967276#32 (by decide), h19]
  · funext a
    rw [hfrT [] (by decide +kernel) (by simp) a (by simp), hS4m]
  · rw [hrelT.reg_same PL3.instrs PL3.run 10#5 (by decide +kernel), hS4r]
  · intro i h1 h2
    rw [RV.Block.regs_same_range PL3.instrs PL3.run hrelT 20 27 (by decide +kernel) i h1 h2, hS4r]

/-- The Horner loop of `poly_eval` placed at any address `A` (callees at their relative offsets), over any table
`C` of field elements at any readable address `T` outside the loop's stack frame; `k` coefficients remain. -/
theorem poly_loop (A T : Word) (C : List Word) (hA : 256 ≤ A.toNat) (hAr : A.toNat + 124 ≤ 4194304)
    (hT : T.toNat + 4 * C.length ≤ 1073741824) (hT4 : T.toNat % 4 = 0) (hC : ∀ i (h : i < C.length), C[i].toNat ≤ P) (k : Nat) :
    ∀ (S : State) (sp0 ra0 v8 v9 v18 v19 x acc : Word),
    1 ≤ k → k ≤ C.length →
    S.pc = A + 60#32 → S.getReg 2#5 = sp0 + 4294967264#32 → S.getReg 9#5 = x → S.getReg 18#5 = BitVec.ofNat 32 k →
    S.getReg 19#5 = T + BitVec.ofNat 32 (4 * (k - 1)) → S.getReg 10#5 = acc →
    acc.toNat ≤ P → acc.toNat % P = polyW (C.drop k) x.toNat % P → x.toNat ≤ P →
    read S.mem (sp0 + 4294967292#32) 4 = ra0 → read S.mem (sp0 + 4294967288#32) 4 = v8 →
    read S.mem (sp0 + 4294967284#32) 4 = v9 → read S.mem (sp0 + 4294967280#32) 4 = v18 →
    read S.mem (sp0 + 4294967276#32) 4 = v19 →
    CodeAt S A Code.poly_eval → CodeAt S (A + 4294967236#32) Code.mul_mod →
    CodeAt S (A + 4294967184#32) Code.add_mod → CodeAt S T C →
    sp0.toNat % 16 = 0 → 4194304 + 48 ≤ sp0.toNat → sp0.toNat ≤ 1073741824 → ra0.toNat % 4 = 0 →
    A.toNat % 4 = 0 → (T.toNat + 4 * C.length + 48 ≤ sp0.toNat ∨ sp0.toNat ≤ T.toNat) →
    ∃ n s', run n S = some s' ∧ s'.pc = ra0 ∧ (s'.getReg 10#5).toNat ≤ P ∧
      (s'.getReg 10#5).toNat % P = polyW C x.toNat % P ∧
      s'.getReg 2#5 = sp0 ∧ s'.getReg 8#5 = v8 ∧ s'.getReg 9#5 = v9 ∧ s'.getReg 18#5 = v18 ∧ s'.getReg 19#5 = v19 ∧
      (∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → s'.getReg i = S.getReg i) ∧
      (∀ a : Word, a.toNat + 48 < sp0.toNat ∨ sp0.toNat ≤ a.toNat → s'.mem a = S.mem a) := by
  induction k with
  | zero => intros; omega
  | succ j ih =>
    intro S sp0 ra0 v8 v9 v18 v19 x acc hk1 hk hpc h2 h9 h18 h19 h10 hacc1 hacc2 hx hm1 hm2 hm3 hm4 hm5
      hcode hmul hadd hcoef hsp hlo hhi hra hA4 hTs
    have hLp : Code.poly_eval.length = 31 := rfl
    have hCb : C.length ≤ 268435456 := by omega
    have hspv : (S.getReg 2#5).toNat = sp0.toNat - 32 := by rw [h2]; bv_omega
    -- words 15–17: `addi x18`, `addi x11`, `jal mul_mod`: one block, then the call
    have hL2 : ((Code.poly_eval.drop 15).take 2).length = 2 := rfl
    have hcA : CodeAt S (A + 60#32) ((Code.poly_eval.drop 15).take 2) := by
      have h := codeAt_take (codeAt_drop hcode 15 (by omega)) 2
      rwa [show A + BitVec.ofNat 32 (4 * 15) = A + 60#32 by bv_omega] at h
    have hjw : read S.mem (A + 60#32 + BitVec.ofNat 32 (4 * ((Code.poly_eval.drop 15).take 2).length)) 4 =
        0xf81ff0ef#32 := by
      rw [hL2, show A + 60#32 + BitVec.ofNat 32 (4 * 2) = A + BitVec.ofNat 32 (4 * 17) by bv_omega]
      exact hcode 17 (by decide)
    obtain ⟨Sj, hrj, hpcj, hraj, hmj, hr2, hr9, hr10, hr18, hr11, hr19, hr20⟩ : ∃ Sj, run 3 S = some Sj ∧
        Sj.pc = A + 4294967236#32 ∧ Sj.getReg 1#5 = A + 72#32 ∧ Sj.mem = S.mem ∧ Sj.getReg 2#5 = S.getReg 2#5 ∧
        Sj.getReg 9#5 = S.getReg 9#5 ∧ Sj.getReg 10#5 = S.getReg 10#5 ∧
        Sj.getReg 18#5 = S.getReg 18#5 + 0xffffffff#32 ∧ Sj.getReg 11#5 = S.getReg 9#5 ∧
        Sj.getReg 19#5 = S.getReg 19#5 ∧ (∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → Sj.getReg i = S.getReg i) := by
      obtain ⟨S', hr, hrel, hromJ, -, hfrJ⟩ := block_jal (code := (Code.poly_eval.drop 15).take 2) PL1.instrs
        PL1.σ S (A + 60#32) 0xffffff80#32 [] [] PL1.dec PL1.run (by rw [hpc]) (by bv_omega)
        (by rw [hL2]; simp only [ROM_END]; bv_omega) hcA 0xf81ff0ef#32 hjw (by decide) (by bv_omega)
        (by simp) (by simp) (by decide +kernel)
      rw [hL2] at hr
      refine ⟨_, by simpa using hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [jal_pc]; bv_omega
      · rw [jal_getReg1]; bv_omega
      · rw [jal_mem]; funext a; exact hfrJ [] (by decide +kernel) (by simp) a (by simp)
      · rw [jal_getReg _ _ _ _ (by decide), hrel.reg_same PL1.instrs PL1.run 2#5 (by decide +kernel)]
      · rw [jal_getReg _ _ _ _ (by decide), hrel.reg_same PL1.instrs PL1.run 9#5 (by decide +kernel)]
      · rw [jal_getReg _ _ _ _ (by decide), hrel.reg_same PL1.instrs PL1.run 10#5 (by decide +kernel)]
      · rw [jal_getReg _ _ _ _ (by decide)]
        exact hrel.reg_addr PL1.instrs PL1.run 18#5 18 0xffffffff#32 (by decide) (by decide +kernel) (by decide +kernel)
      · rw [jal_getReg _ _ _ _ (by decide), hrel.reg_addr PL1.instrs PL1.run 11#5 9 0#32 (by decide)
          (by decide +kernel) (by decide +kernel), BitVec.add_zero]
      · rw [jal_getReg _ _ _ _ (by decide), hrel.reg_same PL1.instrs PL1.run 19#5 (by decide +kernel)]
      · intro i h1 h2
        have hne : i ≠ 1#5 := by rintro rfl; revert h1; decide
        rw [jal_getReg _ _ _ _ hne]
        exact RV.Block.regs_same_range PL1.instrs PL1.run hrel 20 27 (by decide +kernel) i h1 h2
    refine run_of_run S Sj 3 _ hrj ?_
    have hadd' : CodeAt Sj (A + 4294967184#32) Code.add_mod := codeAt_mem_eq hmj hadd
    refine run_callAt (mul_mod_impl (A + 4294967236#32) (by bv_omega)) Sj _ hpcj ?_ ?_ ?_
    · intro c hc
      rw [List.mem_singleton] at hc
      rw [hc, show A + 4294967236#32 + 0xffffffcc#32 = A + 4294967184#32 by bv_omega]
      exact hadd'
    · unfold Call
      show CodeAt Sj Sj.pc Code.mul_mod ∧ Sj.pc.toNat % 4 = 0 ∧ Sj.pc.toNat + 4 * Code.mul_mod.length ≤ ROM_END ∧
        (Sj.getReg 1#5).toNat % 4 = 0 ∧ (Sj.getReg 2#5).toNat % 16 = 0 ∧ ROM_END + 16 ≤ (Sj.getReg 2#5).toNat ∧
        (Sj.getReg 2#5).toNat ≤ RAM_END
      rw [hr2, hspv]
      refine ⟨by rw [hpcj]; exact codeAt_mem_eq hmj hmul, by rw [hpcj]; bv_omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hpcj, show Code.mul_mod.length = 15 from rfl]; simp only [ROM_END]; bv_omega
      · rw [hraj]; bv_omega
      · omega
      · simp only [ROM_END]; omega
      · simp only [RAM_END]; omega
    intro S1 hpc1 hpost1 hcs1 hmem1
    have hpc1' : S1.pc = A + 72#32 := hpc1.trans hraj
    have e10 : Sj.getReg 10 = acc := hr10.trans h10
    have e11 : Sj.getReg 11 = x := hr11.trans h9
    obtain ⟨h1a, h1b⟩ := hpost1 (by rw [e10]; exact hacc1) (by rw [e11]; exact hx)
    rw [e10, e11] at h1b
    have hmemS1 : ∀ a : Word, a.toNat + 16 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S1.mem a = S.mem a := fun a ha =>
      (hmem1 a (by rw [show Sj.getReg 2 = S.getReg 2#5 from hr2]; exact ha)).trans (by rw [hmj])
    have h2' : S1.getReg 2#5 = sp0 + 4294967264#32 := by rw [hcs1 2#5 (by rv_callee_saved), hr2, h2]
    have h9' : S1.getReg 9#5 = x := by rw [hcs1 9#5 (by rv_callee_saved), hr9, h9]
    have h18' : S1.getReg 18#5 = BitVec.ofNat 32 j := by
      rw [hcs1 18#5 (by rv_callee_saved), hr18, h18]; bv_omega
    have h19' : S1.getReg 19#5 = T + BitVec.ofNat 32 (4 * j) := by
      rw [hcs1 19#5 (by rv_callee_saved), hr19, h19, Nat.add_sub_cancel]
    -- word 18 (`lw x11, 0(x19)`): the coefficient `C[j]`; word 19 (`jal add_mod`)
    have hromP : A.toNat + 4 * Code.poly_eval.length ≤ ROM_END := by rw [hLp]; simp only [ROM_END]; omega
    have hrS1 : ∀ b : Word, b.toNat < ROM_END → S1.mem b = S.mem b := fun b hb =>
      hmemS1 b (Or.inl (by simp only [ROM_END] at hb; omega))
    have hcj : read S1.mem (T + BitVec.ofNat 32 (4 * j)) 4 = C[j] := by
      rw [read_of_frame hmemS1 _ 4 (by refine ⟨?_, ?_⟩ <;> bv_omega)]; exact hcoef j (by omega)
    have hTj : (T + BitVec.ofNat 32 (4 * j)).toNat = T.toNat + 4 * j := by bv_omega
    have hL1 : run 1 S1 = some (S1.setReg 11#5 C[j]).nextInstr := by
      rw [run_succ, step_at hcode hA4 hromP hrS1 18 0x0009a583#32 (by decide +kernel) hpc1', decode_poly_eval_0009a583,
        Option.bind_some, exec_load S1 4 true 11#5 19#5 0#32 (by decide) (by simp only [aligned, h19', BitVec.add_zero, hTj]; omega)
          (by simp only [readable, h19', BitVec.add_zero, hTj, RAM_END]; omega), h19', BitVec.add_zero, hcj]
      simp only [↓reduceIte, sext_word]; rfl
    have hJ := run_jal hcode hA4 hromP (T := (S1.setReg 11#5 C[j]).nextInstr) (fun b hb => hrS1 b hb) 19
      0xf45ff0ef#32 (by decide +kernel) (by rw [next_pc, set_pc, hpc1']; bv_omega) 1#5 0xffffff44#32
      decode_poly_eval_f45ff0ef (A + 4294967184#32) (by bv_omega) (by bv_omega)
    obtain ⟨J, hJd⟩ : ∃ J, J = (((S1.setReg 11#5 C[j]).nextInstr.setPC (A + 4294967184#32)).setReg 1#5
        (A + BitVec.ofNat 32 (4 * 19 + 4))) := ⟨_, rfl⟩
    rw [← hJd] at hJ
    have hJr : ∀ i : Reg, ¬ i = 0#5 → i ≠ 1#5 → i ≠ 11#5 → J.getReg i = S1.getReg i := fun i h0 h1 h11 => by
      rw [hJd, jal_getReg _ _ _ _ h1, next_r, r_set_miss _ _ _ _ h0 h11]
    have hJm : J.mem = S1.mem := by rw [hJd, jal_mem, next_mem, set_mem]
    have hJ2 : J.getReg 2#5 = sp0 + 4294967264#32 := (hJr 2#5 (by decide) (by decide) (by decide)).trans h2'
    have hJsp : (J.getReg 2).toNat = sp0.toNat - 32 := by rw [show J.getReg 2 = J.getReg 2#5 from rfl, hJ2]; bv_omega
    have hcallJ : Call J Code.add_mod 16 := by
      unfold Call
      show CodeAt J J.pc Code.add_mod ∧ J.pc.toNat % 4 = 0 ∧ J.pc.toNat + 4 * Code.add_mod.length ≤ ROM_END ∧
        (J.getReg 1#5).toNat % 4 = 0 ∧ (J.getReg 2#5).toNat % 16 = 0 ∧ ROM_END + 16 ≤ (J.getReg 2#5).toNat ∧
        (J.getReg 2#5).toNat ≤ RAM_END
      rw [hJd, jal_pc, jal_getReg1, ← hJd, hJ2]
      refine ⟨codeAt_of_rom hadd (by rw [show Code.add_mod.length = 13 from rfl]; simp only [ROM_END]; bv_omega)
        (fun b hb => by rw [hJm]; exact hrS1 b hb), by bv_omega, ?_, by bv_omega, by bv_omega, ?_, ?_⟩
      · rw [show Code.add_mod.length = 13 from rfl]; simp only [ROM_END]; bv_omega
      · simp only [ROM_END]; bv_omega
      · simp only [RAM_END]; bv_omega
    refine run_of_run S1 J 2 _ (run_trans hL1 hJ) (run_call add_mod_impl J _ hcallJ ?_)
    intro S2 hpc2 hpost2 hcs2 hmem2
    have hJ10 : J.getReg 10 = S1.getReg 10 := hJr 10#5 (by decide) (by decide) (by decide)
    have hJ11 : J.getReg 11 = C[j] := by rw [hJd, jal_getReg _ _ _ _ (by decide), next_r]; exact r_set_hit _ _ _ (by decide)
    simp only [addModPost, hJ10, hJ11] at hpost2
    obtain ⟨h2a, h2b⟩ := hpost2 h1a (hC j (by omega))
    have hpc2' : S2.pc = A + 80#32 := by rw [hpc2, show J.getReg 1 = J.getReg 1#5 from rfl, hJd, jal_getReg1]
    have hslot0 : ∀ a : Word, a.toNat + 16 < sp0.toNat - 32 ∨ sp0.toNat - 32 ≤ a.toNat → S2.mem a = S.mem a := by
      intro a ha
      rw [hmem2 a (by rw [hJsp]; omega), hJm]
      exact hmemS1 a (by omega)
    have h2S2 : S2.getReg 2#5 = sp0 + 4294967264#32 := by rw [hcs2 2#5 (by rv_callee_saved), hJ2]
    have h9S2 : S2.getReg 9#5 = x := by
      rw [hcs2 9#5 (by rv_callee_saved), hJr 9#5 (by decide) (by decide) (by decide), h9']
    have h18S2 : S2.getReg 18#5 = BitVec.ofNat 32 j := by
      rw [hcs2 18#5 (by rv_callee_saved), hJr 18#5 (by decide) (by decide) (by decide), h18']
    have h19S2 : S2.getReg 19#5 = T + BitVec.ofNat 32 (4 * j) := by
      rw [hcs2 19#5 (by rv_callee_saved), hJr 19#5 (by decide) (by decide) (by decide), h19']
    have hS2r : ∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → S2.getReg i = S.getReg i := fun i h1 h2 => by
      rw [hcs2 i (by unfold calleeSaved; bv_omega), hJr i (fun h => by subst h; exact absurd h1 (by decide))
        (fun h => by subst h; exact absurd h1 (by decide)) (fun h => by subst h; exact absurd h1 (by decide))]
      exact (hcs1 i (by unfold calleeSaved; bv_omega)).trans (hr20 i h1 h2)
    have hROM2 : ∀ b : Word, b.toNat < ROM_END → S2.mem b = S.mem b := fun b hb =>
      hslot0 b (Or.inl (by simp only [ROM_END] at hb; omega))
    have hcode2 : CodeAt S2 A Code.poly_eval :=
      codeAt_of_rom hcode (by simp only [ROM_END]; rw [hLp]; omega) hROM2
    obtain ⟨S3, hr3, hpc3, hrel3, -, -, hfr3⟩ := block_branch 20 1 PL2.instrs PL2.σ [] [] PL2.dec PL2.run
      (by decide) (by rw [hpc2']; try rfl) (by bv_omega)
      (by rw [show Code.poly_eval.length = 31 from rfl]; simp only [ROM_END]; bv_omega) hcode2
      0xfe0914e3#32 (by decide +kernel) .ne 18#5 0#5 0xffffffe8#32 decode_poly_eval_fe0914e3 15
      (by decide +kernel) (by simp) (by simp) (by decide +kernel)
    have hmem3 : ∀ a : Word, S3.mem a = S2.mem a := fun a => hfr3 [] (by decide +kernel) (by simp) a (by simp)
    have r0 : S3.getReg 0#5 = 0#32 := r_zero5 S3
    have r18 : S3.getReg 18#5 = BitVec.ofNat 32 j := by
      rw [hrel3.reg_same PL2.instrs PL2.run 18#5 (by decide +kernel), h18S2]
    have r19 : S3.getReg 19#5 = T + BitVec.ofNat 32 (4 * j) + 0xfffffffc#32 := by
      rw [hrel3.reg_addr PL2.instrs PL2.run 19#5 19 0xfffffffc#32 (by decide) (by decide +kernel) (by decide +kernel),
        h19S2]
    have r2 : S3.getReg 2#5 = sp0 + 4294967264#32 := by
      rw [hrel3.reg_same PL2.instrs PL2.run 2#5 (by decide +kernel), h2S2]
    have r9 : S3.getReg 9#5 = x := by
      rw [hrel3.reg_same PL2.instrs PL2.run 9#5 (by decide +kernel), h9S2]
    have r10 : S3.getReg 10#5 = S2.getReg 10#5 := hrel3.reg_same PL2.instrs PL2.run 10#5 (by decide +kernel)
    have hS3r : ∀ i : Reg, 20 ≤ i.toNat → i.toNat ≤ 27 → S3.getReg i = S.getReg i := fun i h1 h2 =>
      (RV.Block.regs_same_range PL2.instrs PL2.run hrel3 20 27 (by decide +kernel) i h1 h2).trans (hS2r i h1 h2)
    -- a saved register's slot (`sp0 - 20 … sp0 - 4`), as before the iteration
    have hslot : ∀ k : Word, 4294967276 ≤ k.toNat → read S3.mem (sp0 + k) 4 = read S.mem (sp0 + k) 4 :=
      fun k hk => read_congr S3.mem S.mem _ 4 (fun j' _ => by
        rw [hmem3, hslot0 _ (Or.inr (by bv_omega))])
    rw [r0, holds_ne0, r18] at hr3
    -- the saved registers and the code, the same in both cases
    have hrom3 : ∀ b : Word, b.toNat < ROM_END → S3.mem b = S.mem b := fun b hb => by rw [hmem3, hROM2 b hb]
    have hcode3 : CodeAt S3 A Code.poly_eval :=
      codeAt_of_rom hcode2 (by simp only [ROM_END]; rw [hLp]; omega) fun b _ => hmem3 b
    have hx1 : read S3.mem (sp0 + 4294967292#32) 4 = ra0 := by
      rw [hslot _ (by decide)]; exact hm1
    have hx8 : read S3.mem (sp0 + 4294967288#32) 4 = v8 := by
      rw [hslot _ (by decide)]; exact hm2
    have hx9 : read S3.mem (sp0 + 4294967284#32) 4 = v9 := by
      rw [hslot _ (by decide)]; exact hm3
    have hx18 : read S3.mem (sp0 + 4294967280#32) 4 = v18 := by
      rw [hslot _ (by decide)]; exact hm4
    have hx19 : read S3.mem (sp0 + 4294967276#32) 4 = v19 := by
      rw [hslot _ (by decide)]; exact hm5
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · -- the last iteration: `bne` falls through to the epilogue
      subst hj0
      rw [show (!decide (BitVec.ofNat 32 0 = 0#32)) = false from rfl] at hr3
      simp only [Bool.false_eq_true, ↓reduceIte] at hr3
      have hpcN : S3.nextInstr.pc = A + 88#32 := by rw [next_pc, hpc3]; bv_omega
      have h2N : S3.nextInstr.getReg 2#5 = sp0 + 4294967264#32 := by rw [next_r, r2]
      obtain ⟨m, S', hrunE, hpcE, hx2E, hx8E, hx9E, hx18E, hx19E, hmemE, hx10E, hregE⟩ :=
        poly_epi A S3.nextInstr sp0 ra0 v8 v9 v18 v19 hA4 hAr hcode3 hpcN h2N hsp hlo hhi hra hx1 hx8 hx9 hx18 hx19
      have hx10 : S'.getReg 10#5 = S2.getReg 10#5 := hx10E.trans (by rw [next_r, r10])
      refine ⟨2 + m, S', run_trans hr3 hrunE, hpcE, ?_, ?_, hx2E, hx8E, hx9E, hx18E, hx19E, ?_, ?_⟩
      · rw [hx10]; exact h2a
      · rw [hx10]
        have e := polyW_drop C x.toNat 0 (by omega)
        rw [List.drop_zero] at e
        rw [e]
        exact horner_step _ _ _ _ _ _ h2b h1b hacc2
      · intro i h1 h2
        exact (hregE i h1 h2).trans (by rw [next_r]; exact hS3r i h1 h2)
      · intro a ha
        rw [congrFun hmemE a, next_mem, hmem3, hslot0 a (by omega)]
    · -- loop again, with `j` coefficients left
      have hne : BitVec.ofNat 32 j ≠ 0#32 := by bv_omega
      rw [decide_eq_false hne] at hr3
      simp only [Bool.not_false, ↓reduceIte] at hr3
      have hpcL : (S3.setPC (A + BitVec.ofNat 32 (4 * 15))).pc = A + 60#32 := by
        rw [jump_pc]
      obtain ⟨n, s', hrun, hp, hA10, hB10, hx2s, hx8s, hx9s, hx18s, hx19s, hregs, hmems⟩ :=
        ih (S3.setPC (A + BitVec.ofNat 32 (4 * 15))) sp0 ra0 v8 v9 v18 v19 x
          (S2.getReg 10#5) (by omega) (by omega) hpcL
          (by rw [jump_r, r2]) (by rw [jump_r, r9]) (by rw [jump_r, r18])
          (by rw [jump_r, r19]; bv_omega) (by rw [jump_r, r10]) h2a
          (by rw [polyW_drop C x.toNat j (by omega)]; exact horner_step _ _ _ _ _ _ h2b h1b hacc2) hx
          hx1 hx8 hx9 hx18 hx19 hcode3
          (codeAt_of_rom hmul (by rw [show Code.mul_mod.length = 15 from rfl]; simp only [ROM_END]; bv_omega) hrom3)
          (codeAt_of_rom hadd (by rw [show Code.add_mod.length = 13 from rfl]; simp only [ROM_END]; bv_omega) hrom3)
          (codeAt_of_mem_range hcoef (by omega) (fun a h1 h2 => by rw [jump_mem, hmem3, hslot0 a (by omega)]))
          hsp hlo hhi hra hA4 hTs
      refine ⟨2 + n, s', run_trans hr3 hrun, hp, hA10, hB10, hx2s, hx8s, hx9s, hx18s, hx19s,
        fun i h1 h2 => (hregs i h1 h2).trans (by rw [jump_r]; exact hS3r i h1 h2), fun a ha => (hmems a ha).trans ?_⟩
      rw [jump_mem, hmem3, hslot0 a (by omega)]
end RV
