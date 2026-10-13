import Slop.RV.Step
import Slop.RV.Attr

/-! Tactics for `Implements` proofs on the RV32 spec (goal-directed symbolic execution).

* `rv_start Code.f hcall`: unpacks the `Call` hypothesis, derives one fetch fact `cᵢ` per instruction,
  and turns the goal into `∃ m s', run m s = some s' ∧ …`.
* `rv_steps n` / `rv_steps n with h₁, …`: executes `n` instructions (fetch from the `cᵢ`, `decode` by the `rv_word`
  lemmas, `exec` per kind, memory by read/write lemmas; side conditions by `bv_omega`).
* `rv_call f_impl` at a `jal` into a proven function, then `intro S1 …` and continue.
* `rv_ret`: stop; the post-conditions about the final state remain.

Notes: literals are kept in `BitVec.ofNat` form (simp normal form) everywhere so that `bv_omega` sees one atom
per register; simp runs with `implicitDefEqProofs := false` (otherwise the kernel re-checks rfl-steps by
unfolding `run`, which blows up); side-condition tactics run without error recovery (`first | … | fail`). -/

namespace RV

open Lean Elab Tactic in
/-- Clears hypotheses `omega` cannot use (fetch facts, code facts, quantified facts): they only slow it down. -/
elab "rv_clear_irrelevant" : tactic => withMainContext do
  let mut ids := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall || (ty.find? fun e => e.isConstOf ``read || e.isConstOf ``CodeAt || e.isConstOf ``run).isSome then
      ids := ids.push d.fvarId
  liftMetaTactic fun g => do return [← g.tryClearMany ids]

open Lean Elab Tactic in
/-- `bv_omega`; with env `RV_DEBUG=1`, reports failures and calls slower than 200 ms (with their goal) to stderr. -/
elab "rv_omega" : tactic => do
  let dbg := (← IO.getEnv "RV_DEBUG").isSome
  let g ← getMainGoal
  let t0 ← IO.monoMsNow
  let report (ok : Bool) : TacticM Unit := do
    let dt := (← IO.monoMsNow) - t0
    if dbg && (dt > 200 || !ok) then IO.eprintln s!"[rv_omega {if ok then "ok" else "FAIL"} {dt} ms] {← Meta.ppGoal g}"
  try
    evalTactic (← `(tactic| bv_omega))
    report true
  catch e =>
    report false
    throw e

open Lean Elab Tactic in
/-- `assumption` up to syntactic equality only (cheap; no unfolding of big terms). -/
elab "rv_assumption" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← instantiateMVars d.type) == t then
      (← getMainGoal).assign d.toExpr; replaceMainGoal []; return
  throwError "rv_assumption: not found"

open Lean Elab Tactic in
/-- `calleeSaved r` for a concrete register (checked syntactically first: no unification with other goals). -/
elab "rv_callee_saved" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOfArity ``calleeSaved 1 do throwError "rv_callee_saved: not a calleeSaved goal"
  evalTactic (← `(tactic| (simp only [calleeSaved]; decide)))

open Lean Elab Tactic in
/-- `decide`, but only on closed goals (fails at once otherwise): register-number (in)equalities. -/
elab "rv_decide_closed" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then throwError "rv_decide_closed: open goal"
  let t0 ← IO.monoMsNow
  try evalTactic (← `(tactic| decide))
  finally
    let dt := (← IO.monoMsNow) - t0
    if (← IO.getEnv "RV_DEBUG").isSome && dt > 20 then IO.eprintln s!"[rv_decide_closed {dt} ms] {← Meta.ppExpr t}"

/-- Side conditions: `calleeSaved` of a concrete register, or arithmetic (`bv_omega`) after reading registers
of the current state (`with h₁, …`: also through an earlier callee's guarantees). -/
syntax "rv_disch" (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_disch $[with $xs,*]?) => do
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← (xs.map (·.getElems) |>.getD #[]).mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| first
      | rv_assumption
      | rv_decide_closed
      | rv_callee_saved
      | ((try simp (disch := first | rv_decide_closed | rv_callee_saved
                                   | (rv_clear_irrelevant; rv_omega) | fail "") only [
            rv_state, reduceRSet, rv_side, BitVec.reduceAdd, BitVec.reduceEq, $xs,*])
         first | rv_decide_closed | (rv_clear_irrelevant; rv_omega))
      | fail "rv_disch")

open Lean Elab Tactic in
/-- `rv_code_facts h Code.f` with `h : CodeAt s a Code.f`: one fetch fact `cᵢ : read s.mem (a + 4i) 4 = wordᵢ` per
instruction (numbered after the facts already in context). -/
elab "rv_code_facts " h:ident code:ident : tactic => do
  let (n, start) ← withMainContext do
    let some d := (← getLCtx).findFromUserName? h.getId | throwError "rv_code_facts: no {h}"
    let ty ← Meta.whnfR (← instantiateMVars d.type)
    let_expr CodeAt _ _ c := ty | throwError "rv_code_facts: not CodeAt"
    let some l ← (Meta.evalNat (← Meta.whnfD (mkApp2 (mkConst ``List.length [0]) (mkConst ``Word) c))).run
      | throwError "rv_code_facts: cannot compute code length"
    let mut k := 0
    while (← getLCtx).findFromUserName? (Name.mkSimple s!"c{k}") |>.isSome do k := k + 1
    pure (l, k)
  for i in [0:n] do
    let c := mkIdent (Name.mkSimple s!"c{start + i}")
    evalTactic (← `(tactic| have $c := $h $(Syntax.mkNumLit (toString i)) (by decide)))
    evalTactic (← `(tactic| simp only [$code:ident, List.getElem_cons_zero, List.getElem_cons_succ, Nat.mul_zero,
      Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceAdd] at $c:ident))

open Lean Elab Tactic in
elab "rv_start " code:ident hcall:ident : tactic => do
  let hcode := mkIdent `hcode
  let (hpc, hrom, hra, hsp, hlo, hhi) := (mkIdent `hpc, mkIdent `hrom, mkIdent `hra, mkIdent `hsp, mkIdent `hlo,
    mkIdent `hhi)
  evalTactic (← `(tactic| obtain ⟨$hcode, $hpc, $hrom, $hra, $hsp, $hlo, $hhi⟩ := $hcall:ident))
  evalTactic (← `(tactic| unfold Returns))
  evalTactic (← `(tactic| simp only [$code:ident, List.length_cons, List.length_nil, ROM_END, RAM_END,
    BitVec.ofNat_eq_ofNat] at $hpc $hrom $hlo $hhi $hra $hsp ⊢))
  evalTactic (← `(tactic| rv_code_facts $hcode $code:ident))

open Lean Elab Tactic in
/-- The fetch facts `cᵢ` in the local context, as simp lemmas. -/
def factLemmas : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    let s := d.userName.toString
    if !d.isImplementationDetail && s.startsWith "c" && s.length > 1 && (s.drop 1).all Char.isDigit then
      out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):ident))
  return out

open Lean Elab Tactic Meta in
/-- For every store `write _ a _ n` in the goal, adds `hw : writable a n` once (proved by `rv_disch`), so that later
side conditions about the same store (e.g. fetch-after-store, `read_write_rom`) close by `assumption`. -/
def addWritableFacts : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut seen : Array Expr := #[]
  for d in ← getLCtx do
    seen := seen.push (← instantiateMVars d.type)
  let ref ← IO.mkRef (#[] : Array (Expr × Expr))
  forEachExpr tgt fun sub => do
    if sub.isAppOfArity ``write 4 then
      let p := (sub.getArg! 1, sub.getArg! 3)
      unless (← ref.get).any (· == p) do ref.modify (·.push p)
  let found ← ref.get
  for (a, n) in found do
    let ty := mkApp2 (mkConst ``writable) a n
    if seen.any (· == ty) then continue
    let pmv ← mkFreshExprSyntheticOpaqueMVar ty
    let gs ← Tactic.run pmv.mvarId! (evalTactic (← `(tactic| rv_disch)))
    if gs.isEmpty then
      let g ← getMainGoal
      let g' ← g.assert (← mkFreshUserName `hw) ty (← instantiateMVars pmv)
      let (_, g'') ← g'.intro1P
      replaceMainGoal [g'']
      seen := seen.push ty

open Lean Elab Tactic in
/-- One symbolic step's simplification (fetch, decode, exec) on the current goal. -/
def rvStepSimp (ext : Array Term) : TacticM Unit := do
  let ex ← ext.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  -- side conditions only need register facts, not the (conditional, expensive) memory-frame rewrites
  let dext := ext.filter fun t => !(t.raw.getHead?.map (·.getId.toString.startsWith "read_of_frame")).getD false
  let facts := (← factLemmas) ++ ex
  evalTactic (← `(tactic| simp (config := { implicitDefEqProofs := false }) (disch := rv_disch with $dext,*) only [
    rv_exec, rv_state, reduceRSet, rv_word, and_not_one_of_aligned, BitVec.reduceAdd, BitVec.reduceEq,
    BitVec.reduceSetWidth, BitVec.reduceToNat, $facts,*]))

open Lean Elab Tactic in
def rvSteps (n : Nat) (ext : Array Term) : TacticM Unit := do
  for _ in [0:n] do
    evalTactic (← `(tactic| apply run_of_step))
    rvStepSimp ext
    addWritableFacts

open Lean Elab Tactic in
/-- `rv_step_simp with h₁, …`: the simplification of one step, on any goal mentioning `step S`. -/
elab "rv_step_simp" " with " xs:term,* : tactic => rvStepSimp xs.getElems

open Lean Elab Tactic in
/-- `rv_steps n`: execute `n` instructions. -/
elab "rv_steps " n:num : tactic => rvSteps n.getNat #[]

open Lean Elab Tactic in
/-- `rv_steps n with h₁, h₂`: also rewrite with the given facts (e.g. what a returned call guarantees). -/
elab "rv_steps " n:num " with " xs:term,* : tactic => do
  rvSteps n.getNat xs.getElems

macro "rv_ret" : tactic => `(tactic| apply run_done)

/-- `CodeAt S a code` for a state `S` built from one where `hc : CodeAt s a code` holds (through register writes,
jumps, RAM stores and returned calls). -/
syntax "rv_codeAt " ident ident (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_codeAt $hc:ident $code:ident $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← xs'.mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      repeat first
        | with_reducible apply codeAt_set | with_reducible apply codeAt_next | with_reducible apply codeAt_jump
        | (with_reducible apply codeAt_store _ _ _ _ _ _ _ (by first | rv_decide_closed | ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch)) (by rv_disch))
        | (refine codeAt_of_frame ?_ ‹_› ?_
           repeat (with_reducible apply codeMem_write _ _ _ _ (by first | rv_decide_closed | ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch)) (by rv_disch))
           try apply codeMem_of_codeAt)
      all_goals first
        | ((try simp only [set_pc, next_pc, jump_pc, store_pc, BitVec.add_assoc, BitVec.reduceAdd,
              BitVec.ofNat_eq_ofNat]); exact $hc)
        | ((try simp (disch := rv_disch with $xs',*) only [List.length_cons, List.length_nil, $code:ident, reduceRSet,
              next_r, store_r, jump_r, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat, $xs,*]);
           rv_disch with $xs',*)))

/-- Proves `Call S code frame` at a call site (`with h₁, …`: an earlier callee's register guarantees). -/
syntax "rv_call_ok " ident ident (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_call_ok $hc:ident $code:ident $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← (xs.map (·.getElems) |>.getD #[]).mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      simp (disch := rv_disch with $xs',*) only [Call, $code:ident, List.length_cons, List.length_nil, BitVec.ofNat_eq_ofNat,
        reduceRSet, next_r, store_r, jump_r, set_pc, next_pc, jump_pc, store_pc, BitVec.reduceEq, ite_true, ite_false,
        $xs,*]
      refine ⟨?_, (by rv_disch with $xs',*), (by rv_disch with $xs',*), (by rv_disch with $xs',*),
        (by rv_disch with $xs',*), (by rv_disch with $xs',*), (by rv_disch with $xs',*)⟩
      rv_codeAt $hc $code with $xs',*))

/-- After `apply run_call f_impl` and `rv_call_ok`: name what the callee guarantees, in normal form. -/
syntax "rv_returned " ident ident ident ident ident (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_returned $S1:ident $hpc:ident $hpost:ident $hcs:ident $hmem:ident $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← xs'.mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intro $S1:ident $hpc:ident $hpost:ident $hcs:ident $hmem:ident
      try simp only [fn₁, reduceRSet, next_r, store_r, jump_r, BitVec.reduceEq, ite_true, ite_false,
        BitVec.ofNat_eq_ofNat] at $hpc:ident $hpost:ident ⊢
      try simp only [BitVec.ofNat_eq_ofNat] at $hcs:ident
      try simp (disch := rv_disch with $xs',*) only [BitVec.ofNat_eq_ofNat, reduceRSet, next_r, store_r, jump_r,
        set_mem, next_mem, store_mem, jump_mem, BitVec.reduceEq, ite_true, ite_false, $xs,*] at $hmem:ident))

/-- Register reads of the final state, for concrete register numbers (`rv_regs at h`: in a hypothesis). -/
syntax "rv_regs" (" at " ident)? : tactic
macro_rules
  | `(tactic| rv_regs) => `(tactic|
    simp only [fn₁, reduceRSet, next_r, store_r, jump_r, set_pc, jump_pc, next_pc, store_pc, BitVec.reduceAdd,
      BitVec.add_assoc, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat])
  | `(tactic| rv_regs at $h:ident) => `(tactic|
    simp only [fn₁, reduceRSet, next_r, store_r, jump_r, set_pc, jump_pc, next_pc, store_pc, BitVec.reduceAdd,
      BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat] at $h:ident)

/-- Callee-saved registers of the final state: one case per register (`with h₁, …`: through callees). -/
syntax "rv_callee" (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_callee $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let i := Lean.mkIdent `i
    let hi := Lean.mkIdent `hi
    let mut pre ← `(tactic| intro $i $hi)
    let mut names : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for k in [0:xs'.size] do
      let h := Lean.mkIdent (Lean.Name.mkSimple s!"hcs_{k}")
      pre ← `(tactic| ($pre; have $h := $(xs'[k]!) $i $hi))
      names := names.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
    `(tactic| (
      $pre:tactic
      rcases calleeSaved_cases $i $hi with h|h|h|h|h|h|h|h|h|h|h|h|h
      all_goals subst h
      all_goals simp only [BitVec.ofNat_eq_ofNat, reduceRSet, next_r, store_r, jump_r, BitVec.reduceEq, ite_true,
        ite_false, $names,*]))

/-- Memory of the final state outside the frame (`with h₁, …`: callees' frame guarantees, register facts). -/
syntax "rv_frame" (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_frame $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← xs'.mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intro a ha
      simp (disch := rv_disch with $xs',*) only [set_mem, jump_mem, next_mem, store_mem, write_outside, $xs,*]))

end RV
