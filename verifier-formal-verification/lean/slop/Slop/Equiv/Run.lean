import Slop.Equiv.RunLemmas
import Slop.Equiv.Walk
import Slop.Equiv.Regs

/-! `sail_run hs`: walk a goal `runF M σ = r` through Sail code on an Airbender state (`hs : Sys σ`).
At each step it first tries to evaluate the whole rest in the kernel (`oracle_run`: fixed registers only);
otherwise it takes one step at the head: `pure`/bind/`if` with a closed condition, register reads and writes
(the `Sys` proof is carried across writes to volatile registers), `currentlyEnabled`, `SailME.run`, or unfolding
a definition. It stops at anything it cannot decide (typically a condition on a symbolic address), leaving that
goal; prove that condition and call it again. -/

open Lean Meta Elab Tactic
open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem oracle_run_eq {α : Type} {σ : FState} (hs : Airbender.Sys σ) (m : SailM α) (a : α) {r}
    (h : runOracle knownDemo (fun _ => none) m = some a) (hr : EStateM.Result.ok a σ = r) : runF m σ = r := by
  rw [oracle_run hs m a h]; exact hr

theorem run_congr {α : Type} {m m' : SailM α} (h : m = m') (σ : FState) {r} (h' : runF m' σ = r) :
    runF m σ = r := by subst h; exact h'

theorem me_run_bind_ite_true {α β : Type} {G : Bool} {A B : SailME β α} (f : α → SailME β β) (hG : G = true) :
    PreSail.PreSailME.run ((if G = true then A else B) >>= f) = PreSail.PreSailME.run (A >>= f) := by subst hG; rfl
theorem me_run_bind_ite_false {α β : Type} {G : Bool} {A B : SailME β α} (f : α → SailME β β) (hG : G = false) :
    PreSail.PreSailME.run ((if G = true then A else B) >>= f) = PreSail.PreSailME.run (B >>= f) := by subst hG; rfl
theorem me_run_ite_true' {β : Type} {G : Bool} {A B : SailME β β} (hG : G = true) :
    PreSail.PreSailME.run (if G = true then A else B) = PreSail.PreSailME.run A := by subst hG; rfl
theorem me_run_ite_false' {β : Type} {G : Bool} {A B : SailME β β} (hG : G = false) :
    PreSail.PreSailME.run (if G = true then A else B) = PreSail.PreSailME.run B := by subst hG; rfl

theorem run_bind_ok2 {α β : Type} (m : SailM α) (f : α → SailM β) (σ σ' : FState) (a : α) {r}
    (hm : runF m σ = .ok a σ') (h : runF (f a) σ' = r) : runF (m >>= f) σ = r := by
  rw [Slop.runF_bind_ok m f σ σ' a hm]; exact h

theorem sys_xset {σ : FState} (hs : Airbender.Sys σ) (i : BitVec 5) (v : BitVec 32) : Airbender.Sys (xset σ i v) := by
  intro r hr
  rw [xset_regs σ i v r (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; simp [Airbender.Volatile] at hr))]
  exact hs r hr

theorem sys_of_regs {σ σ' : FState} (hs : Airbender.Sys σ) (h : σ'.regs = σ.regs) : Airbender.Sys σ' := by
  intro r hr; rw [h]; exact hs r hr

theorem run_memRead_bind {β γ : Type} (req : MemRequest)
    (cont : InstructionEffect.ret (.memRead req) → SailM γ) (f : γ → SailM β) (σ : FState) {r}
    (h : runF (cont (.ok (readBytes σ.mem req.address.toNat req.size, 0#req.numTag)) >>= f) σ = r) :
    runF (FreeM.impure (.inl (.ok (.memRead req))) cont >>= f) σ = r := h

/-- `runOracle knownDemo (no memory) m = some v`, proven by the kernel, if the kernel computes it. -/
def oracleValue (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let q ← mkAppM ``runOracle #[mkConst ``knownDemo, ← mkFunUnit, m]
  let some r := (Kernel.whnf (← getEnv) (← getLCtx) q).toOption | return none
  unless r.isAppOfArity ``Option.some 2 do return none
  let v := r.getArg! 1
  let ty ← mkEq q (← mkAppM ``Option.some #[v])
  let pf ← try withOptions (fun o => maxRecDepth.set o 1000000) (mkAuxTheorem ty (← mkEqRefl q))
    catch _ => return none
  return some (v, pf)

/-- A Bool condition: closed ones by the kernel, others by the side tactic (if given). -/
def closedBool (side : Option Syntax) (G : Expr) : MetaM (Option (Bool × Expr)) := do
  if !(G.hasFVar || G.hasMVar) then
    for b in [true, false] do
      try return some (b, ← kernelDecide (← mkEq G (toExpr b))) catch _ => pure ()
    return none
  let some tac := side | do logInfo m!"sail_run: undecided condition (no side tactic){indentExpr G}"; return none
  let mut notes : Array MessageData := #[]
  for b in [true, false] do
    let mv ← mkFreshExprSyntheticOpaqueMVar (← mkEq G (toExpr b))
    let saved ← Core.getMessageLog
    let (ok, note) ← try
        let gs ← Elab.Term.TermElabM.run' <| Tactic.run mv.mvarId! (evalTactic tac)
        let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
        let note := m!"b={b}: {gs.length} goals left, {errs.length} errors" ++
          (match errs.head? with | some e => m!"; {e.data}" | none => m!"") ++
          (match gs.head? with | some g' => m!"; goal {g'}" | none => m!"")
        pure (gs.isEmpty && errs.isEmpty, note)
      catch ex => pure (false, m!"b={b}: exception {ex.toMessageData}")
    Core.setMessageLog saved
    if ok then return some (b, ← instantiateMVars mv)
    notes := notes.push note
  for n in notes do logInfo m!"side tactic {n}"
  logInfo m!"sail_run: undecided condition{indentExpr G}"
  return none

/-- Rewrite the program in the goal `runF M σ = r` by `h : M = M'`. -/
def rewriteProg (g : MVarId) (M M' σ r h : Expr) : MetaM MVarId := g.withContext do
  step1 g ``run_congr #[none, M, M', h, σ, r]

/-- Head normal form without unfolding definitions, also through `have` (`letFun`). -/
partial def whnfC (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  if e.isAppOfArity ``letFun 4 then
    return ← whnfC (Expr.headBeta (mkApp (e.getArg! 3) (e.getArg! 2)))
  return e

/-- Prove a proposition with the side tactic (or by assumption). -/
def proveSide (side : Option Syntax) (p : Expr) : MetaM (Option Expr) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar p
  let saved ← Core.getMessageLog
  let ok ← try
      let tac ← match side with
        | some s => `(tactic| first | assumption | $(⟨s⟩))
        | none => `(tactic| assumption)
      let gs ← Elab.Term.TermElabM.run' <| Tactic.run mv.mvarId! (evalTactic tac)
      pure (gs.isEmpty && !(← Core.getMessageLog).hasErrors)
    catch _ => pure false
  Core.setMessageLog saved
  if ok then return some (← instantiateMVars mv) else return none

/-- Apply a proven layer lemma `∀ …, hyps → runF pat σ = .ok v σ'` to the action `m` at state `σ`:
`(v, σ', proof of runF m σ = .ok v σ')`. Hypotheses: `Sys` by `hs`, others by the side tactic. -/
def applyLayer (side : Option Syntax) (hs : Expr) (lem : Expr) (m σ : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← inferType lem
  let (args, _, concl) ← forallMetaTelescopeReducing ty
  let some (_, lhs, rhs) := concl.eq? | return none
  unless lhs.isAppOfArity ``runF 3 do return none
  unless ← isDefEq (lhs.getArg! 1) m do return none
  unless ← isDefEq (lhs.getArg! 2) σ do return none
  let rhs ← instantiateMVars rhs
  unless rhs.isAppOf ``EStateM.Result.ok do return none
  for a in args do
    if (← instantiateMVars a).isMVar then
      let aty ← instantiateMVars (← inferType a)
      if aty.isAppOf ``Airbender.Sys then
        unless ← isDefEq a hs do return none
      else if (← isProp aty) then
        let some p ← proveSide side aty | return none
        unless ← isDefEq a p do return none
  let pf ← instantiateMVars (mkAppN lem args)
  if pf.hasExprMVar then return none
  let rhs ← instantiateMVars rhs
  return some (rhs.getArg! 3, rhs.getArg! 4, pf)

/-- One step inside `SailME.run X`: `(Y, h : run X = Y)`, or `none` if undecided. -/
def meStep (side : Option Syntax) (X0 : Expr) : MetaM (Option (Expr × Expr)) := do
  let X ← whnfC X0
  let runX ← mkAppM ``PreSail.PreSailME.run #[X]
  let ret (h : Expr) : MetaM (Option (Expr × Expr)) := do
    let h ← mkExpectedTypeHint h (← mkEq runX (← inferType h).eq?.get!.2.2)
    return some ((← inferType h).eq?.get!.2.2, h)
  if X.isAppOfArity ``Bind.bind 6 then
    let (m, f) := (X.getArg! 4, X.getArg! 5)
    let m' ← whnfC m
    if m'.isAppOf ``liftM then return ← ret (← mkAppM ``me_run_lift_bind #[m'.appArg!, f])
    if m'.isAppOfArity ``Pure.pure 4 then return ← ret (← mkAppM ``me_run_pure_bind #[m'.getArg! 3, f])
    if m'.isAppOfArity ``Bind.bind 6 then
      return ← ret (← mkAppM ``me_run_bind_assoc #[m'.getArg! 4, m'.getArg! 5, f])
    if m'.isAppOf ``SailME.throw || m'.isAppOf ``PreSail.PreSailME.throw then
      return ← ret (← mkAppM ``me_run_throw_bind #[m'.appArg!, f])
    if m'.isAppOfArity ``ite 5 then
      let some (_, G, _) := (m'.getArg! 1).eq? | return none
      let some (b, pG) ← closedBool side G | return none
      return ← ret (← mkAppOptM (if b then ``me_run_bind_ite_true else ``me_run_bind_ite_false)
        #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, pG])
    if let some m'' ← delta? m' (fun _ => true) then
      let X' := mkAppN X.getAppFn (X.getAppArgs.set! 4 m'')
      let Y ← mkAppM ``PreSail.PreSailME.run #[X']
      return some (Y, ← mkExpectedTypeHint (← mkEqRefl runX) (← mkEq runX Y))
    return none
  if X.isAppOfArity ``ite 5 then
    let some (_, G, _) := (X.getArg! 1).eq? | return none
    let some (b, pG) ← closedBool side G | return none
    return ← ret (← mkAppOptM (if b then ``me_run_ite_true' else ``me_run_ite_false') #[none, G, X.getArg! 3, X.getArg! 4, pG])
  if X.isAppOfArity ``Pure.pure 4 then
    return ← ret (← mkAppM ``me_run_pure #[X.getArg! 3])
  if let some X' ← delta? X (fun _ => true) then
    let Y ← mkAppM ``PreSail.PreSailME.run #[X']
    return some (Y, ← mkExpectedTypeHint (← mkEqRefl runX) (← mkEq runX Y))
  let inner ← if X.isAppOfArity ``Bind.bind 6 then do
      let m ← whnfC (X.getArg! 4); pure m!" first action: {m.getAppFn} ({m.getAppNumArgs} args)"
    else pure m!""
  logInfo m!"meStep: stuck at {X.getAppFn} ({X.getAppNumArgs} args){inner}"
  return none

theorem run_congr_bind {α β : Type} {m m' : SailM α} (h : m = m') (f : α → SailM β) (σ : FState) {r}
    (h' : runF (m' >>= f) σ = r) : runF (m >>= f) σ = r := by subst h; exact h'

partial def sailRunLoop (side : Option Syntax) (lemmas : Array Expr) (g0 : MVarId) (hs0 : Expr) (fuel : Nat) : MetaM (MVarId × Expr × String) := do
  let mut g := g0
  let mut hs := hs0
  for _ in [0:fuel] do
    let (M, σ, r) ← g.withContext (splitGoal g)
    let M ← whnfC M
    g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runF #[M, σ]) r))
    if M.isAppOfArity ``Pure.pure 4 then return (g, hs, "done (pure)")
    -- 1. the whole rest, by the kernel
    if let some (v, pf) ← g.withContext (oracleValue M) then
      g ← g.withContext (step1 g ``oracle_run_eq #[none, σ, hs, M, v, r, pf])
      return (g, hs, "done (kernel)")
    -- 2. one step at the head
    if M.isAppOfArity ``ite 5 then
      let some (_, G, _) := (M.getArg! 1).eq? | return (g, hs, "ite: not Bool")
      match ← g.withContext (closedBool side G) with
      | some (false, pG) => g ← g.withContext (step1 g ``run_ite_false #[none, G, M.getArg! 3, M.getArg! 4, σ, r, pG])
      | some (true, pG) => g ← g.withContext (step1 g ``run_ite_true #[none, G, M.getArg! 3, M.getArg! 4, σ, r, pG])
      | none => return (g, hs, "stopped at a condition")
      continue
    if M.isAppOf ``PreSail.PreSailME.run then
      match ← g.withContext (meStep side M.appArg!) with
      | some (Y, h) => g ← rewriteProg g M Y σ r h; continue
      | none => return (g, hs, "stopped in SailME")
    if M.isAppOfArity ``Bind.bind 6 then
      let (m, f) := (M.getArg! 4, M.getArg! 5)
      let m' ← whnfC m
      if m'.isAppOfArity ``Pure.pure 4 then
        g ← g.withContext (step1 g ``run_pure_bind #[none, none, m'.getArg! 3, f, σ, r]); continue
      if m'.isAppOfArity ``Bind.bind 6 then
        g ← g.withContext (step1 g ``run_bind_assoc #[none, none, none, m'.getArg! 4, m'.getArg! 5, f, σ, r]); continue
      if m'.isAppOfArity ``ite 5 then
        let some (_, G, _) := (m'.getArg! 1).eq? | return (g, hs, "bind ite: not Bool")
        match ← g.withContext (closedBool side G) with
        | some (false, pG) =>
          g ← g.withContext (step1 g ``run_bind_ite_false #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, σ, r, pG])
        | some (true, pG) =>
          g ← g.withContext (step1 g ``run_bind_ite_true #[none, none, G, m'.getArg! 3, m'.getArg! 4, f, σ, r, pG])
        | none => return (g, hs, "stopped at a condition (bind)")
        continue
      if m'.isAppOf ``rX_bits && m'.appArg!.isAppOfArity ``regidx.Regidx 1 then
        let hm ← g.withContext (mkAppM ``rX_run #[m'.appArg!.appArg!, σ])
        let v ← g.withContext (mkAppM ``xget #[σ, m'.appArg!.appArg!])
        g ← g.withContext (step1 g ``run_bind_ok #[none, none, m', f, σ, v, r, hm]); continue
      if m'.isAppOf ``wX_bits && (m'.getArg! 0).isAppOfArity ``regidx.Regidx 1 then
        let (i, v) := ((m'.getArg! 0).appArg!, m'.getArg! 1)
        let hm ← g.withContext (mkAppM ``wX_run #[i, v, σ])
        let σ' ← g.withContext (mkAppM ``xset #[σ, i, v])
        hs ← g.withContext (mkAppM ``sys_xset #[hs, i, v])
        g ← g.withContext (step1 g ``run_bind_ok2 #[none, none, m', f, σ, σ', toExpr (), r, hm]); continue
      if m'.isAppOf ``readReg then
        g ← g.withContext (step1 g ``run_readReg_bind #[none, m'.appArg!, f, σ, r]); continue
      if m'.isAppOf ``writeReg then
        let (reg, v) := (m'.getArg! (m'.getAppNumArgs - 2), m'.appArg!)
        let hv ← g.withContext (kernelDecide (← mkEq (← mkAppM ``Airbender.Volatile #[reg]) (toExpr true)))
        hs ← g.withContext (mkAppM ``sys_set #[hs, reg, v, hv])
        g ← g.withContext (step1 g ``run_writeReg_bind #[none, reg, v, f, σ, r]); continue
      if m'.isAppOf ``PreSail.PreSailME.run then
        match ← g.withContext (meStep side m'.appArg!) with
        | some (Y, h) => g ← g.withContext (step1 g ``run_congr_bind #[none, none, m', Y, h, f, σ, r]); continue
        | none => return (g, hs, "stopped in SailME (bind)")
      if m'.isAppOf ``FreeM.impure then
        let eff := m'.getArg! (m'.getAppNumArgs - 2)
        if eff.isAppOf ``Sum.inl && eff.appArg!.isAppOf ``Except.ok && eff.appArg!.appArg!.isAppOf ``InstructionEffect.memRead then
          let req := eff.appArg!.appArg!.appArg!
          g ← g.withContext (step1 g ``run_memRead_bind #[none, none, req, m'.appArg!, f, σ, r]); continue
      let mut usedLemma := false
      for lem in lemmas do
        if let some (v, σ', hm) ← g.withContext (applyLayer side hs lem m' σ) then
          if !(← g.withContext (isDefEq σ' σ)) then
            let regsEq ← g.withContext do
              let lhs ← mkAppM ``Human.FState.regs #[σ']
              let rhs ← mkAppM ``Human.FState.regs #[σ]
              mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
            hs ← g.withContext (mkAppM ``sys_of_regs #[hs, regsEq])
          g ← g.withContext (step1 g ``run_bind_ok2 #[none, none, m', f, σ, σ', v, r, hm])
          usedLemma := true
          break
      if usedLemma then continue
      if let some (v, pf) ← g.withContext (oracleValue m') then
        let hm ← g.withContext (mkAppM ``oracle_run #[hs, m', v, pf])
        g ← g.withContext (step1 g ``run_bind_ok #[none, none, m', f, σ, v, r, hm]); continue
      if let some m'' ← delta? m' (fun _ => true) then
        let M' := mkAppN M.getAppFn (M.getAppArgs.set! 4 m'')
        g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runF #[M', σ]) r)); continue
      return (g, hs, "stopped at an action")
    if let some M' ← delta? M (fun _ => true) then
      g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runF #[M', σ]) r)); continue
    return (g, hs, "stopped")
  return (g, hs, "out of fuel")

def sailRun (hs : Syntax) (side : Option Syntax) (lemmas : Array Syntax := #[]) : TacticM Unit := withMainContext do
  let hs ← elabTerm hs none
  let lemmas ← lemmas.mapM fun l => elabTerm l none
  let (g, _, msg) ← sailRunLoop side lemmas (← getMainGoal) hs 2000
  replaceMainGoal [g]
  logInfo m!"sail_run: {msg}"

syntax (name := sailRunUsing) "sail_run " term " using " tactic : tactic
elab_rules : tactic
  | `(tactic| sail_run $hs using $tac) => sailRun hs (some tac)
elab "sail_run " hs:term : tactic => sailRun hs none
syntax (name := sailRunWith) "sail_run " term " using " tactic " with " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| sail_run $hs using $tac with [$ls,*]) => sailRun hs (some tac) ls.getElems

end Slop.Equiv
