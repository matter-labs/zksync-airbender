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

/-- Side conditions proven so far (goal ↦ proof): the same ones come back at every step. -/
initialize rvOmegaCache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr) ← IO.mkRef {}

open Lean Elab Tactic in
/-- `bv_omega`, reusing the proof of an identical goal proven before when all its free variables are still in scope
(the kernel checks the reused proof like any other); with env `RV_DEBUG=1`, reports failures and calls slower than
200 ms (with their goal) to stderr. -/
elab "rv_omega" : tactic => withMainContext do
  let dbg := (← IO.getEnv "RV_DEBUG").isSome
  let g ← getMainGoal
  let key ← instantiateMVars (← g.getType)
  -- `calleeSaved r` is decided by `rv_callee_saved`; omega would only fail slowly
  if key.isAppOfArity ``calleeSaved 1 then throwError "rv_omega: calleeSaved goal"
  if !key.hasMVar then
    if let some pf := (← rvOmegaCache.get)[key]? then
      let lctx ← getLCtx
      if !pf.hasAnyFVar (fun f => !lctx.contains f) then
        g.assign pf; replaceMainGoal []; return
  let t0 ← IO.monoMsNow
  let report (ok : Bool) : TacticM Unit := do
    let dt := (← IO.monoMsNow) - t0
    if dbg && (dt > 200 || !ok) then IO.eprintln s!"[rv_omega {if ok then "ok" else "FAIL"} {dt} ms] {← Meta.ppGoal g}"
    if (← IO.getEnv "RV_STATS").isSome then
      IO.eprintln s!"[rv_omega_stat {if ok then "ok" else "FAIL"} {dt}] {(toString (← Meta.ppExpr (← instantiateMVars (← g.getType)))).replace "\n" " "}"
  try
    evalTactic (← `(tactic| bv_omega))
    report true
    if !key.hasMVar then
      let pf ← instantiateMVars (mkMVar g)
      if !pf.hasMVar then rvOmegaCache.modify (·.insert key pf)
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

open Lean Elab Tactic in
/-- Fails on a `calleeSaved r` goal (decided by `rv_callee_saved` alone: never worth an `omega` call). -/
elab "rv_not_callee_goal" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  if t.isAppOfArity ``calleeSaved 1 then throwError "rv_not_callee_goal"

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
      | (rv_not_callee_goal
         (try simp (disch := first | rv_decide_closed | rv_callee_saved
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
/-- `rv_code_facts_range h Code.f lo hi`: fetch facts `cᵢ` only for instructions `lo ≤ i < hi` of a (long) function
(each word read off the list once, at elaboration time; checked by `rfl`). -/
elab "rv_code_facts_range " h:ident code:ident lo:num hi:num : tactic => do
  let some cname := (← resolveGlobalConst code).head? | throwError "rv_code_facts_range: unknown {code}"
  let words ← unsafe Meta.evalExpr (List (BitVec 32)) (← Meta.inferType (mkConst cname)) (mkConst cname)
  let start ← withMainContext do
    let mut k := 0
    while (← getLCtx).findFromUserName? (Name.mkSimple s!"c{k}") |>.isSome do k := k + 1
    pure k
  for i in [lo.getNat:hi.getNat] do
    let c := mkIdent (Name.mkSimple s!"c{start + i - lo.getNat}")
    let w := Syntax.mkNumLit (toString (words[i]!).toNat)
    let iS := Syntax.mkNumLit (toString i)
    evalTactic (← `(tactic| set_option maxRecDepth 100000 in
      have $c : read _ (_ + BitVec.ofNat 32 (4 * $iS)) 4 = BitVec.ofNat 32 $w :=
        ($h $iS (by decide)).trans (by rfl)))
    evalTactic (← `(tactic| simp only [Nat.mul_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.reduceAdd] at $c:ident))

open Lean Elab Tactic in
/-- Clears the fetch facts `cᵢ` (e.g. after moving on to a new state whose code facts are derived afresh). -/
elab "rv_clear_facts" : tactic => withMainContext do
  let mut ids := #[]
  for d in ← getLCtx do
    let s := d.userName.toString
    if !d.isImplementationDetail && s.startsWith "c" && s.length > 1 && (s.drop 1).all Char.isDigit then
      ids := ids.push d.fvarId
  liftMetaTactic fun g => do return [← g.tryClearMany ids]

open Lean Elab Tactic Meta in
/-- `rv_name T hT`: in a goal `∃ m s', run m X = some s' ∧ …`, names the current state: `hT : X = T`. -/
elab "rv_name " T:ident hT:ident : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some X := tgt.find? fun e => e.isAppOfArity ``RV.run 2 && !(e.getArg! 1).hasLooseBVars
    | throwError "rv_name: no `run _ X` in the goal"
  let Xs ← Term.exprToSyntax (X.getArg! 1)
  evalTactic (← `(tactic| generalize $hT:ident : $Xs = $T:ident))

open Lean Elab Tactic in
/-- `nat_cases i hi` with `hi : i < n` (literal `n`): one goal per value `i = 0, …, n-1` (substituted). -/
elab "nat_cases " i:ident hi:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? hi.getId | throwError "nat_cases: no {hi}"
  let ty ← instantiateMVars d.type
  let_expr LT.lt _ _ _ nE := ty | throwError "nat_cases: not `i < n`"
  let some n ← (Meta.evalNat nE).run | throwError "nat_cases: bound not a literal"
  if n == 0 then evalTactic (← `(tactic| omega)); return
  let mut disj ← `($i = $(Syntax.mkNumLit (toString (n - 1))))
  for k in (List.range (n - 1)).reverse do
    disj ← `($i = $(Syntax.mkNumLit (toString k)) ∨ $disj)
  let h := mkIdent `hcase
  evalTactic (← `(tactic| have $h : $disj := by omega))
  for _ in [0:n - 1] do
    evalTactic (← `(tactic| all_goals try obtain $h | $h := ($h : _ ∨ _)))
  evalTactic (← `(tactic| all_goals subst $h:ident))

open Lean Elab Tactic in
elab "rv_start " code:ident hcall:ident : tactic => do
  let hcode := mkIdent `hcode
  let (hpc, hrom, hra, hsp, hlo, hhi) := (mkIdent `hpc, mkIdent `hrom, mkIdent `hra, mkIdent `hsp, mkIdent `hlo,
    mkIdent `hhi)
  evalTactic (← `(tactic| obtain ⟨$hcode, $hpc, $hrom, $hra, $hsp, $hlo, $hhi⟩ := $hcall:ident))
  evalTactic (← `(tactic| try unfold Returns))
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
/-- The facts `cut_…` about the current state left by `rv_cut`. -/
def cutLemmas : TacticM (Array Term) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail && d.userName.toString.startsWith "cut_" then
      out := out.push (mkIdent d.userName)
  return out

open Lean Elab Tactic in
/-- One symbolic step's simplification (fetch, decode, exec) on the current goal. -/
def rvStepSimp (ext : Array Term) : TacticM Unit := do
  let ex ← ext.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  -- side conditions only need register facts, not the (conditional, expensive) memory-frame rewrites
  let dext := ext.filter fun t => !(t.raw.getHead?.map (·.getId.toString.startsWith "read_of_frame")).getD false
  let cuts ← cutLemmas
  let facts := (← factLemmas) ++ ex ++ (← cuts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
  let dext := dext ++ cuts
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

open Lean Elab Tactic Meta in
/-- Number of nodes of `e`, up to `bound`; closed subterms (literals, types, instances) count as one. -/
partial def exprSizeUpTo (e : Expr) (bound : Nat) : Nat :=
  let rec go (e : Expr) (acc : Nat) : Nat :=
    if acc ≥ bound then acc else
    if !e.hasFVar then acc + 1 else
    match e with
    | .app f a => go a (go f (acc + 1))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b (acc + 1)
    | _ => acc + 1
  go e 0

open Lean Elab Tactic Meta in
/-- After `rv_cut`: big register values (and stored values in `cut_mem`) become fresh variables `cv_k` with
`cvdef_k : value = cv_k` kept aside (not used by the step simp), so the goal stays small. Undo with `subst_vars`. -/
def rvAbstractValues (bound : Nat := 25) : TacticM Unit := withMainContext do
  let lctx ← getLCtx
  let cuts := lctx.foldl (init := #[]) fun acc d =>
    if !d.isImplementationDetail && d.userName.toString.startsWith "cut_r" || d.userName == `cut_mem then
      acc.push d else acc
  let mut next := 0
  for d in lctx do
    let n := d.userName.toString
    if n.startsWith "cv_" then
      if let some k := (n.drop 3).toNat? then next := max next (k + 1)
  let mut cands : Array Expr := #[]
  for d in cuts do
    let ty ← instantiateMVars d.type
    let_expr Eq _ _ rhs := ty | continue
    if d.userName == `cut_mem then
      let ref ← IO.mkRef (#[] : Array Expr)
      forEachExpr rhs fun sub => do
        if sub.isAppOfArity ``write 4 then
          let v := sub.getArg! 2
          if exprSizeUpTo v bound ≥ bound && !v.hasLooseBVars then ref.modify (·.push v)
      for v in ← ref.get do
        unless cands.contains v do cands := cands.push v
    else if exprSizeUpTo rhs bound ≥ bound then
      unless cands.contains rhs do cands := cands.push rhs
  let locs := cuts.map fun d => mkIdent d.userName
  for e in cands do
    let es ← Term.exprToSyntax e
    let v := mkIdent (Name.mkSimple s!"cv_{next}")
    let h := mkIdent (Name.mkSimple s!"cvdef_{next}")
    next := next + 1
    evalTactic (← `(tactic| generalize $h:ident : $es = $v:ident at $locs*))

/-- `rv_cut`: in a goal `∃ m s', run m X = some s' ∧ …`, replaces the (grown) state term `X` by a fresh state with
facts `cut_pc`, `cut_mem`, `cut_r1 … cut_r31`, `cut_input` giving its PC, memory, registers and input in normal form (in terms of the
start state). Later `rv_steps` use them, so the cost of a step no longer grows with the number of steps taken.
Facts of an earlier cut are consumed and cleared. `rv_cut with h₁, …`: also normalize with `hᵢ` (e.g. a returned
call's `∀ i, calleeSaved i → S₁.getReg i = …`, discharged by `rv_callee_saved`). -/
syntax "rv_cut" (" with " term,*)? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic | `(tactic| rv_cut $[with $xs,*]?) => withMainContext do
  let extra : Array Term := xs.map (·.getElems) |>.getD #[]
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some runX := tgt.find? fun e => e.isAppOfArity ``RV.run 2 && !(e.getArg! 1).hasLooseBVars
    | throwError "rv_cut: no `run _ X` in the goal"
  let X := runX.getArg! 1
  let old := (← getLCtx).foldl (init := #[]) fun acc d =>
    if !d.isImplementationDetail && d.userName.toString.startsWith "cut_" then acc.push d.userName else acc
  let lhs (k : Nat) (S : Expr) : MetaM Expr :=
    if k = 0 then mkAppM ``State.pc #[S] else if k = 1 then mkAppM ``State.mem #[S]
    else if k = 33 then mkAppM ``State.input #[S] else do
      mkAppM ``State.getReg #[S, ← mkAppOptM ``OfNat.ofNat #[mkApp (mkConst ``BitVec) (mkNatLit 5),
        mkRawNatLit (k - 1), none]]
  let names := #["pc", "mem"] ++ (List.range 31).toArray.map (fun i => s!"r{i + 1}") ++ #["input"]
  -- new goal: ∀ S, S.pc = X.pc → S.mem = X.mem → S.getReg 1 = X.getReg 1 → … → G[S]; the right-hand sides are
  -- then normalized by `simp` (with the facts of the previous cut)
  let newTy ← withLocalDeclD `S (mkConst ``State) fun S => do
    let mut body := tgt.replace fun e => if e == X then some S else none
    for k in (List.range names.size).reverse do
      body := mkForall `_ .default (← mkEq (← lhs k S) (← lhs k X)) body
    mkForallFVars #[S] body
  let m ← mkFreshExprSyntheticOpaqueMVar newTy
  let mut prfs := #[]
  for k in [0:names.size] do prfs := prfs.push (← mkEqRefl (← lhs k X))
  g.assign (mkAppN m (#[X] ++ prfs))
  let (_, g1) ← m.mvarId!.introN 1 [`S]
  let tmp := names.map fun n => Name.mkSimple s!"cutnew_{n}"
  let (_, g2) ← g1.introN names.size tmp.toList
  replaceMainGoal [g2]
  let oldL ← old.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let extraL ← extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  let allL := oldL ++ extraL
  let locs := tmp.map mkIdent
  evalTactic (← `(tactic| try simp (config := { implicitDefEqProofs := false }) (disch := rv_callee_saved) only [
    rv_state, reduceRSet, BitVec.reduceAdd, $allL,*] at $locs*))
  withMainContext do
    let g ← getMainGoal
    let mut g := g
    for n in old do
      if let some d := (← g.getDecl).lctx.findFromUserName? n then g ← g.tryClear d.fvarId
    for (t, n) in tmp.zip names do
      if let some d := (← g.getDecl).lctx.findFromUserName? t then g ← g.rename d.fvarId (Name.mkSimple s!"cut_{n}")
    replaceMainGoal [g]
  rvAbstractValues

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
        | (refine codeAt_store_disj _ _ _ _ _ _ ?_ (by ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch with $xs',*)) (by ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch with $xs',*)) (by rv_disch with $xs',*))
        | (with_reducible apply codeAt_store _ _ _ _ _ _ _ (by first | rv_decide_closed | ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch)) (by rv_disch))
        | (refine codeAt_of_frame ?_ ‹_› ?_
           repeat first
             | (refine codeMem_write_disj _ _ _ ?_ (by ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch with $xs',*)) (by ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch with $xs',*)) (by rv_disch with $xs',*))
             | (with_reducible apply codeMem_write _ _ _ _ (by first | rv_decide_closed | ((try simp only [List.length_cons, List.length_nil, $code:ident]); rv_disch)) (by rv_disch))
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

/-- `rv_call_ok` when only registers and the PC changed since `hc : CodeAt S …` (no stores): `CodeAt` by memory
equality, never by searching through frames. -/
syntax "rv_call_ok_mem " ident ident (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_call_ok_mem $hc:ident $code:ident $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← (xs.map (·.getElems) |>.getD #[]).mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    let cme := Lean.mkIdent `RV.codeAt_mem_eq
    `(tactic| (
      simp (disch := rv_disch with $xs',*) only [Call, $code:ident, List.length_cons, List.length_nil, BitVec.ofNat_eq_ofNat,
        reduceRSet, next_r, store_r, jump_r, set_pc, next_pc, jump_pc, store_pc, BitVec.reduceEq, ite_true, ite_false,
        $xs,*]
      refine ⟨?_, (by rv_disch with $xs',*), (by rv_disch with $xs',*), (by rv_disch with $xs',*),
        (by rv_disch with $xs',*), (by rv_disch with $xs',*), (by rv_disch with $xs',*)⟩
      exact $cme (by simp only [rv_state]) $hc))

/-- After `apply run_call f_impl` and `rv_call_ok`: name what the callee guarantees, in normal form. -/
syntax "rv_returned " ident ident ident ident ident (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_returned $S1:ident $hpc:ident $hpost:ident $hcs:ident $hmem:ident $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← xs'.mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intro $S1:ident $hpc:ident $hpost:ident $hcs:ident $hmem:ident
      try simp only [mapsA0, reduceRSet, next_r, store_r, jump_r, BitVec.reduceEq, ite_true, ite_false,
        BitVec.ofNat_eq_ofNat] at $hpc:ident $hpost:ident ⊢
      try simp only [BitVec.ofNat_eq_ofNat] at $hcs:ident
      try simp (disch := rv_disch with $xs',*) only [BitVec.ofNat_eq_ofNat, reduceRSet, next_r, store_r, jump_r,
        set_mem, next_mem, store_mem, jump_mem, BitVec.reduceEq, ite_true, ite_false, $xs,*] at $hmem:ident))

/-- Register reads of the final state, for concrete register numbers (`rv_regs at h`: in a hypothesis). -/
syntax "rv_regs" (" at " ident)? : tactic
macro_rules
  | `(tactic| rv_regs) => `(tactic|
    simp only [mapsA0, reduceRSet, next_r, store_r, jump_r, set_pc, jump_pc, next_pc, store_pc, BitVec.reduceAdd,
      BitVec.add_assoc, BitVec.reduceEq, ite_true, ite_false, BitVec.ofNat_eq_ofNat])
  | `(tactic| rv_regs at $h:ident) => `(tactic|
    simp only [mapsA0, reduceRSet, next_r, store_r, jump_r, set_pc, jump_pc, next_pc, store_pc, BitVec.reduceAdd,
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

/-- A conditional branch, stepped by hand (`rv_steps` cannot decide a condition on symbolic values, and its
automatic side conditions loop on some backward branches): `with hpc, h₁, …` facts to decide it. -/
syntax "rv_branch_taken" " with " ident ("," term)* : tactic
macro_rules
  | `(tactic| rv_branch_taken with $hpc:ident $[, $xs]*) => `(tactic| (
    apply run_of_step
    rv_step_simp with $hpc
    rw [exec_branch_t _ _ _ _ _ (by rv_regs; first | decide | simp only [$[$xs:term],*]; done)
      (by rv_regs; first | (rw [$hpc:ident]; bv_omega) | bv_omega)]
    simp only [Option.elim_some]))

syntax "rv_branch_not_taken" " with " ident ("," term)* : tactic
macro_rules
  | `(tactic| rv_branch_not_taken with $hpc:ident $[, $xs]*) => `(tactic| (
    apply run_of_step
    rv_step_simp with $hpc
    rw [exec_branch_f _ _ _ _ _ (by rv_regs; first | decide | simp only [$[$xs:term],*]; done)]
    simp only [Option.elim_some]))

end RV
