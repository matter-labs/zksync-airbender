import Slop.Sym.Sound
import Mathlib.Tactic.IntervalCases

/-! # Running a straight-line block with the symbolic executor -/

namespace RV.Sym

variable (c : Ctx)

/-- The side conditions only grow along a run, and the pool only extends. -/
theorem symRun_mono : ∀ (instrs : List Instr) (S : State) (σ σ' : SState), Rel c σ S → CondsOK σ →
    symRun instrs σ = some σ' → CondsOK σ' ∧ Ext c σ.pool σ'.pool ∧ ∀ x ∈ σ.conds, x ∈ σ'.conds
  | [], S, σ, σ', hrel, hcok, hrun => by
    simp only [symRun, Option.some.injEq] at hrun; subst hrun
    exact ⟨hcok, Ext.refl c _ hrel.1, fun _ h => h⟩
  | i :: is, S, σ, σ', hrel, hcok, hrun => by
    simp only [symRun] at hrun
    obtain ⟨σ1, h1, hrun⟩ := Option.bind_eq_some_iff.mp hrun
    obtain ⟨k1, e1, s1, S1, -, hrel1, -⟩ := symStep_sound c σ σ1 S i hrel hcok h1
    obtain ⟨k', e', s'⟩ := symRun_mono is S1 σ1 σ' hrel1 k1 hrun
    exact ⟨k', e1.trans c e', fun x hx => s' x (s1 x hx)⟩

/-- A straight-line block of code: if the symbolic run succeeds and its side conditions hold, the machine runs the
block (one step per word) to a state that the final symbolic state denotes; ROM is unchanged. -/
theorem run_block : ∀ (code : List Word) (instrs : List Instr) (S : State) (σ σ' : SState) (A : Word),
    code.map decode = instrs.map some → Rel c σ S → CondsOK σ → S.pc = A → A.toNat % 4 = 0 →
    A.toNat + 4 * code.length ≤ ROM_END → CodeAt S A code → symRun instrs σ = some σ' →
    (∀ x ∈ σ'.conds, x.Holds c σ') →
    CondsOK σ' ∧ Ext c σ.pool σ'.pool ∧ (∀ x ∈ σ.conds, x ∈ σ'.conds) ∧
    ∃ S', run code.length S = some S' ∧ S'.pc = A + BitVec.ofNat 32 (4 * code.length) ∧ Rel c σ' S' ∧
      ∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b
  | [], instrs, S, σ, σ', A, hdec, hrel, hcok, hpc, _, _, _, hrun, _ => by
    cases instrs with
    | nil =>
      simp only [symRun, Option.some.injEq] at hrun; subst hrun
      exact ⟨hcok, Ext.refl c _ hrel.1, fun _ h => h, S, rfl, by simp [hpc], hrel, fun _ _ => rfl⟩
    | cons _ _ => simp at hdec
  | w :: ws, instrs, S, σ, σ', A, hdec, hrel, hcok, hpc, hal, hrom, hcode, hrun, hconds => by
    cases instrs with
    | nil => simp at hdec
    | cons i is =>
      simp only [List.map_cons, List.cons.injEq] at hdec
      obtain ⟨hw, hdec⟩ := hdec
      simp only [symRun] at hrun
      obtain ⟨σ1, h1, hrun⟩ := Option.bind_eq_some_iff.mp hrun
      obtain ⟨k1, e1, s1, S1, hpc1, hrel1, hex⟩ := symStep_sound c σ σ1 S i hrel hcok h1
      have hlen : (w :: ws).length = ws.length + 1 := rfl
      obtain ⟨-, e'', s''⟩ := symRun_mono c is S1 σ1 σ' hrel1 k1 hrun
      have hc1 : ∀ x ∈ σ1.conds, x.Holds c σ1 := fun x hx =>
        (holds_ext c e'' σ1 σ' rfl rfl x (k1 x hx)).mp (hconds x (s'' x hx))
      obtain ⟨hex, hrom1⟩ := hex hc1
      -- the rest of the block, from `S1`
      have hcode1 : CodeAt S1 (A + 4#32) ws := by
        intro j hj
        rw [read_congr S1.mem S.mem _ 4 (fun t ht => hrom1 _ (by simp only [List.length_cons, ROM_END] at hrom ⊢; bv_omega))]
        have := hcode (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [← this]; congr 1; bv_omega
      obtain ⟨k', e', s', S', hrun', hpc', hrel', hrom'⟩ := run_block ws is S1 σ1 σ' (A + 4#32) hdec hrel1 k1
        (by rw [hpc1, hpc]; rfl) (by bv_omega) (by simp only [List.length_cons] at hrom; bv_omega) hcode1 hrun hconds
      refine ⟨k', e1.trans c e', fun x hx => s' x (s1 x hx), S', ?_, ?_, hrel', fun b hb => (hrom' b hb).trans (hrom1 b hb)⟩
      · rw [hlen, run_succ, step_fetch S w (by rw [hpc]; exact hal) (by rw [hpc]; simp only [List.length_cons] at hrom; omega)
          (by have := hcode 0 (by simp); simpa [hpc] using this), hw, Option.bind_some, hex, Option.bind_some, hrun']
      · rw [hpc']; simp only [List.length_cons]; bv_omega

end RV.Sym

namespace RV.Sym

/-- The context of a block starting in state `S`: register `i` is `S.getReg i`, memory is `S.mem`. -/
def ctxOf (S : State) : Ctx := ⟨fun i => S.getReg (BitVec.ofNat 5 i), S.mem⟩

/-- `WFNodes`, decided. -/
def wfB : List Node → Bool
  | [] => true
  | n :: ns => n.childLt ns.length && wfB ns

theorem wfB_spec : ∀ ns : List Node, wfB ns = true → WFNodes ns
  | [], _ => trivial
  | n :: ns, h => by
    simp only [wfB, Bool.and_eq_true] at h
    exact ⟨h.1, wfB_spec ns h.2⟩

theorem initPool_wf : initPool.WF := ⟨wfB_spec _ (by decide), rfl, rfl⟩

theorem initPool_val (S : State) (i : Nat) (hi : i < 32) :
    initPool.val (ctxOf S) i = S.getReg (BitVec.ofNat 5 i) := by
  interval_cases i <;> rfl

theorem rel_init (S : State) : Rel (ctxOf S) initState S := by
  refine ⟨initPool_wf, rfl, fun r => ?_, fun w hw => by simp [initState] at hw, ?_⟩
  · have hr : initState.reg r = ⟨r.toNat, r.toNat, 0⟩ := by
      simp only [initState, SState.reg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range r.isLt]; rfl
    rw [hr]
    refine ⟨⟨r.isLt, r.isLt, by simp⟩, ?_⟩
    simp only [initState]; rw [initPool_val S _ r.isLt]; simp
  · rfl

theorem condsOK_init : CondsOK initState := fun x hx => by simp [initState] at hx

end RV.Sym
