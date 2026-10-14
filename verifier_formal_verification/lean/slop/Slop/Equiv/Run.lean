import Slop.Equiv.RunLemmas
import Slop.Equiv.Walk
import Slop.Equiv.Regs
import Slop.Equiv.NormAttr
import Slop.Sail.KernelRfl

/-! `sail_run hs`: walk a goal `runSail M σ = r` through Sail code on an Airbender state (`hs : Configured σ`).
At each step it first tries to evaluate the whole rest in the kernel (`oracle_run`: fixed registers only);
otherwise it takes one step at the head: `pure`/bind/`if` with a closed condition, register reads and writes
(the `Configured` proof is carried across writes to volatile registers), `currentlyEnabled`, `SailME.run`, or unfolding
a definition. It stops at anything it cannot decide (typically a condition on a symbolic address), leaving that
goal; prove that condition and call it again. -/

open Lean Meta Elab Tactic
open Sail Sail.ArchSem SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem oracle_run_eq {α : Type} {σ : SailState} (hs : Airbender.Configured σ) (m : SailM α) (a : α) {r}
    (h : runOracle knownDemo (fun _ => none) m = some a) (hr : EStateM.Result.ok a σ = r) : runSail m σ = r := by
  rw [oracle_run hs m a h]; exact hr

theorem run_pure_eq {α : Type} (a : α) (σ : SailState) {r} (h : EStateM.Result.ok a σ = r) :
    runSail (pure a : SailM α) σ = r := by rw [Slop.runF_pure]; exact h

theorem run_congr {α : Type} {m m' : SailM α} (h : m = m') (σ : SailState) {r} (h' : runSail m' σ = r) :
    runSail m σ = r := by subst h; exact h'

theorem me_run_bind_ite_true {α β : Type} {G : Bool} {A B : SailME β α} (f : α → SailME β β) (hG : G = true) :
    PreSail.PreSailME.run ((if G = true then A else B) >>= f) = PreSail.PreSailME.run (A >>= f) := by subst hG; rfl
theorem me_run_bind_ite_false {α β : Type} {G : Bool} {A B : SailME β α} (f : α → SailME β β) (hG : G = false) :
    PreSail.PreSailME.run ((if G = true then A else B) >>= f) = PreSail.PreSailME.run (B >>= f) := by subst hG; rfl
theorem me_run_ite_true' {β : Type} {G : Bool} {A B : SailME β β} (hG : G = true) :
    PreSail.PreSailME.run (if G = true then A else B) = PreSail.PreSailME.run A := by subst hG; rfl
theorem me_run_ite_false' {β : Type} {G : Bool} {A B : SailME β β} (hG : G = false) :
    PreSail.PreSailME.run (if G = true then A else B) = PreSail.PreSailME.run B := by subst hG; rfl

theorem run_bind_ok2 {α β : Type} (m : SailM α) (f : α → SailM β) (σ σ' : SailState) (a : α) {r}
    (hm : runSail m σ = .ok a σ') (h : runSail (f a) σ' = r) : runSail (m >>= f) σ = r := by
  rw [Slop.runF_bind_ok m f σ σ' a hm]; exact h

theorem sys_xset {σ : SailState} (hs : Airbender.Configured σ) (i : BitVec 5) (v : BitVec 32) : Airbender.Configured (xset σ i v) := by
  intro r hr
  rw [xset_regs σ i v r (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; simp [Airbender.writtenByProgram] at hr))]
  exact hs r hr

theorem sys_of_regs {σ σ' : SailState} (hs : Airbender.Configured σ) (h : σ'.regs = σ.regs) : Airbender.Configured σ' := by
  intro r hr; rw [h]; exact hs r hr

theorem run_memRead_bind {β γ : Type} (req : MemRequest)
    (cont : InstructionEffect.ret (.memRead req) → SailM γ) (f : γ → SailM β) (σ : SailState) {r}
    (h : runSail (cont (.ok (readBytes σ.mem req.address.toNat req.size, 0#req.numTag)) >>= f) σ = r) :
    runSail (FreeM.impure (.inl (.ok (.memRead req))) cont >>= f) σ = r := h

/-- Reading a register that is as after reset, whose reset value `v` is known. -/
theorem run_readReg_bind_sys {β : Type} {σ : SailState} (hs : Airbender.Configured σ) (r : Register)
    (hv : Airbender.writtenByProgram r = false) (v : RegisterType r) (hr : Airbender.resetState.regs r = v)
    (f : RegisterType r → SailM β) {res} (h : runSail (f v) σ = res) : runSail (readReg r >>= f) σ = res := by
  rw [Slop.runF_bind, Slop.runF_readReg, hs r hv, hr]; exact h

theorem run_memWrite_bind {β γ : Type} (req : MemRequest) (v : BitVec (8 * req.size)) (tags : BitVec req.numTag)
    (cont : InstructionEffect.ret (.memWrite req v tags) → SailM γ) (f : γ → SailM β) (σ : SailState) {r}
    (h : runSail (cont (.ok ()) >>= f) { σ with mem := Human.writeBytes σ.mem req.address.toNat req.size v } = r) :
    runSail (FreeM.impure (.inl (.ok (.memWrite req v tags))) cont >>= f) σ = r := h

theorem run_memWriteAnnounce_bind {β γ : Type} (req : MemRequest)
    (cont : InstructionEffect.ret (.memWriteAnnounce req) → SailM γ) (f : γ → SailM β) (σ : SailState) {r}
    (h : runSail (cont () >>= f) σ = r) :
    runSail (FreeM.impure (.inl (.ok (.memWriteAnnounce req))) cont >>= f) σ = r := h

/-- `runOracle knownDemo (no memory) m = some v`, proven by the kernel, if the kernel computes it. -/
initialize oracleMs : IO.Ref Nat ← IO.mkRef 0
initialize oracleCalls : IO.Ref Nat ← IO.mkRef 0

def oracleValue (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let t0 ← IO.monoMsNow
  let res ← oracleValueCore m
  oracleMs.modify (· + ((← IO.monoMsNow) - t0)); oracleCalls.modify (· + 1)
  return res
where oracleValueCore (m : Expr) : MetaM (Option (Expr × Expr)) := do
  let q ← mkAppM ``runOracle #[mkConst ``knownDemo, ← mkFunUnit, m]
  let some r := (Kernel.whnf (← getEnv) (← getLCtx) q).toOption | return none
  unless r.isAppOfArity ``Option.some 2 do return none
  let v := r.getArg! 1
  let ty ← mkEq q (← mkAppM ``Option.some #[v])
  let pf ← try mkAuxTheoremNow ty (← mkEqRefl q)
    catch _ => return none
  return some (v, pf)

/-- Normalize with the `sail_norm` simp set: `(e', proof e = e')`, or `none` if nothing changes. -/
def normExpr (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let some ext ← getSimpExtension? `sail_norm | return none
  let thms ← ext.getTheorems
  let ctx ← Simp.mkContext (config := { decide := true }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp e ctx (simprocs := #[← Simp.getSimprocs])
  if r.expr == e then return none
  return some (r.expr, ← r.getProof)

/-- A Bool condition: closed ones by the kernel, others by the side tactic (if given). -/
def closedBool (side : Option Syntax) (G : Expr) : MetaM (Option (Bool × Expr)) := do
  if !(G.hasFVar || G.hasMVar) then
    -- normalize first (e.g. the privilege after reset is `Machine`), so the kernel never re-runs the reset
    let (G', pn) ← match ← normExpr G with
      | some (G', p) => pure (G', some p)
      | none => pure (G, none)
    let t0 ← IO.monoMsNow
    -- compute the value (compiled code), then let the kernel check `G' = value`
    let some b ← (try some <$> (unsafe evalExpr Bool (mkConst ``Bool) G') catch _ => pure none) | return none
    let ty ← mkEq G' (toExpr b)
    let pf ← try mkAuxTheoremNow ty (← mkEqRefl G')
      catch _ => return none
    let pf ← match pn with | some p => mkEqTrans p pf | none => pure pf
    return some (b, pf)
  let some tac := side | do logInfo m!"sail_run: undecided condition (no side tactic){indentExpr G}"; return none
  let mut notes : Array MessageData := #[]
  let tside ← IO.monoMsNow
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
    trace[debug] "side tactic b={b} ok={ok} after {(← IO.monoMsNow) - tside} ms on{indentExpr G}"
    if ok then return some (b, ← instantiateMVars mv)
    notes := notes.push note
  for n in notes do logInfo m!"side tactic {n}"
  logInfo m!"sail_run: undecided condition{indentExpr G}"
  return none

/-- Rewrite the program in the goal `runSail M σ = r` by `h : M = M'`. -/
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

/-- Normalize an action with the `sail_norm` simp set: `(m', proof m = m')`. -/
def normAction (m : Expr) : MetaM (Option (Expr × Expr)) := normExpr m

/-- Apply a proven layer lemma `∀ …, hyps → runSail pat σ = .ok v σ'` to the action `m` at state `σ`:
`(v, σ', proof of runSail m σ = .ok v σ')`. Hypotheses: `Configured` by `hs`, others by the side tactic. -/
def applyLayer (side : Option Syntax) (hs : Expr) (lem : Expr) (m σ : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let ty ← inferType lem
  let (args, _, concl) ← forallMetaTelescopeReducing ty
  let some (_, lhs, rhs) := concl.eq? | return none
  unless lhs.isAppOfArity ``runSail 3 do return none
  -- cheap filter: same head function as the lemma's program
  unless (lhs.getArg! 1).getAppFn.constName? == m.getAppFn.constName? do return none
  unless ← withReducible (isDefEq (lhs.getArg! 1) m) do
    trace[debug] "applyLayer: no match{indentExpr m}\nvs{indentExpr (lhs.getArg! 1)}"
    return none
  unless ← isDefEq (lhs.getArg! 2) σ do return none
  let rhs ← instantiateMVars rhs
  unless rhs.isAppOf ``EStateM.Result.ok do return none
  for a in args do
    if (← instantiateMVars a).isMVar then
      let aty ← instantiateMVars (← inferType a)
      if aty.isAppOf ``Airbender.Configured then
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
  let t0 ← IO.monoMsNow
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
      let t1 ← IO.monoMsNow
      let some (b, pG) ← closedBool side G | return none
      trace[debug] "meStep: ite condition {(← IO.monoMsNow) - t1} ms{indentExpr G}"
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

theorem run_congr_bind {α β : Type} {m m' : SailM α} (h : m = m') (f : α → SailM β) (σ : SailState) {r}
    (h' : runSail (m' >>= f) σ = r) : runSail (m >>= f) σ = r := by subst h; exact h'

partial def sailRunLoop (side : Option Syntax) (lemmas : Array Expr) (g0 : MVarId) (hs0 : Expr) (fuel : Nat)
    (wholeRest : Bool := true) : MetaM (MVarId × Expr × String) := do
  let mut g := g0
  let mut hs := hs0
  -- whole-rest kernel attempts back off after failures (they fail until the symbolic part is passed)
  let mut wait : Nat := 0
  let mut backoff : Nat := 1
  for _ in [0:fuel] do
    let (M, σ, r) ← g.withContext (splitGoal g)
    let M ← whnfC M
    g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runSail #[M, σ]) r))
    if M.isAppOfArity ``Pure.pure 4 then
      g ← g.withContext (step1 g ``run_pure_eq #[none, M.getArg! 3, σ, r])
      return (g, hs, "done (pure)")
    -- 1. the whole rest, by the kernel (never while the reset state is mentioned: it would be re-evaluated)
    if wholeRest && wait == 0 && !M.containsConst (· == ``Airbender.resetState) then
      if let some (v, pf) ← g.withContext (oracleValue M) then
        g ← g.withContext (step1 g ``oracle_run_eq #[none, σ, hs, M, v, r, pf])
        return (g, hs, "done (kernel)")
      wait := backoff; backoff := backoff * 2
    else wait := wait - 1
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
      if m'.isAppOf ``FreeM.pure then
        g ← g.withContext (step1 g ``run_pure_bind #[none, none, m'.appArg!, f, σ, r]); continue
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
        let reg := m'.appArg!
        -- a register as after reset with a `sail_norm` value (e.g. the privilege is `Machine`): use the value
        let known ← g.withContext do
          let r0 ← mkAppM ``Human.SailState.regs #[mkConst ``Airbender.resetState, reg]
          let some (v, hr) ← normExpr r0 | return none
          if v.containsConst (· == ``Airbender.resetState) then return none
          let hv ← try kernelDecide (← mkEq (← mkAppM ``Airbender.writtenByProgram #[reg]) (toExpr false)) catch _ => return none
          return some (v, hv, hr)
        if let some (v, hv, hr) := known then
          g ← g.withContext (step1 g ``run_readReg_bind_sys #[none, none, hs, reg, hv, v, hr, f, r]); continue
        g ← g.withContext (step1 g ``run_readReg_bind #[none, reg, f, σ, r]); continue
      if m'.isAppOf ``writeReg then
        let (reg, v) := (m'.getArg! (m'.getAppNumArgs - 2), m'.appArg!)
        let hv ← g.withContext (kernelDecide (← mkEq (← mkAppM ``Airbender.writtenByProgram #[reg]) (toExpr true)))
        hs ← g.withContext (mkAppM ``sys_set #[hs, reg, v, hv])
        g ← g.withContext (step1 g ``run_writeReg_bind #[none, reg, v, f, σ, r]); continue
      -- arguments mentioning the reset state: rewrite them first (e.g. its privilege is `Machine`)
      if m'.containsConst (· == ``Airbender.resetState) then
        match ← g.withContext (normAction m') with
        | some (m2, h) =>
          g ← g.withContext (step1 g ``run_congr_bind #[none, none, m', m2, h, f, σ, r]); continue
        | none => pure ()
      if m'.isAppOf ``PreSail.PreSailME.run then
        match ← g.withContext (meStep side m'.appArg!) with
        | some (Y, h) => g ← g.withContext (step1 g ``run_congr_bind #[none, none, m', Y, h, f, σ, r]); continue
        | none => return (g, hs, "stopped in SailME (bind)")
      if m'.isAppOf ``FreeM.impure then
        let eff := m'.getArg! (m'.getAppNumArgs - 2)
        if eff.isAppOf ``Sum.inl && eff.appArg!.isAppOf ``Except.ok && eff.appArg!.appArg!.isAppOf ``InstructionEffect.memRead then
          let req := eff.appArg!.appArg!.appArg!
          g ← g.withContext (step1 g ``run_memRead_bind #[none, none, req, m'.appArg!, f, σ, r]); continue
        if eff.isAppOf ``Sum.inl && eff.appArg!.isAppOf ``Except.ok && eff.appArg!.appArg!.isAppOf ``InstructionEffect.memWriteAnnounce then
          let req := eff.appArg!.appArg!.appArg!
          g ← g.withContext (step1 g ``run_memWriteAnnounce_bind #[none, none, req, m'.appArg!, f, σ, r]); continue
        if eff.isAppOf ``Sum.inl && eff.appArg!.isAppOf ``Except.ok && eff.appArg!.appArg!.isAppOf ``InstructionEffect.memWrite then
          let w := eff.appArg!.appArg!
          let k := w.getAppNumArgs
          let (req, v, tags) := (w.getArg! (k - 3), w.getArg! (k - 2), w.getArg! (k - 1))
          -- registers unchanged: still an Airbender state
          let σ' ← g.withContext do
            let addr ← mkAppM ``BitVec.toNat #[← mkAppM ``MemRequest.address #[req]]
            let mem ← mkAppM ``Human.writeBytes #[← mkAppM ``Human.SailState.mem #[σ], addr, ← mkAppM ``MemRequest.size #[req], v]
            mkAppM ``Human.SailState.mk #[← mkAppM ``Human.SailState.regs #[σ], mem]
          hs ← g.withContext do
            let lhs ← mkAppM ``Human.SailState.regs #[σ']
            let rhs ← mkAppM ``Human.SailState.regs #[σ]
            mkAppM ``sys_of_regs #[hs, ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)]
          g ← g.withContext (step1 g ``run_memWrite_bind #[none, none, req, v, tags, m'.appArg!, f, σ, r]); continue
      let mut usedLemma := false
      for lem in lemmas do
        if let some (v, σ', hm) ← g.withContext (applyLayer side hs lem m' σ) then
          if !(← g.withContext (isDefEq σ' σ)) then
            let regsEq ← g.withContext do
              let lhs ← mkAppM ``Human.SailState.regs #[σ']
              let rhs ← mkAppM ``Human.SailState.regs #[σ]
              mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
            hs ← g.withContext (mkAppM ``sys_of_regs #[hs, regsEq])
          g ← g.withContext (step1 g ``run_bind_ok2 #[none, none, m', f, σ, σ', v, r, hm])
          usedLemma := true
          break
      if usedLemma then continue
      -- a layer lemma for this function, but arguments not in normal form: normalize them and retry
      if lemmas.any (fun l => (l.getAppFn.constName?.isSome)) then
        let heads ← lemmas.filterMapM fun l => do
          let (_, _, c) ← forallMetaTelescopeReducing (← inferType l)
          pure ((c.eq?.map (·.2.1)).bind fun lhs => (lhs.getArg! 1).getAppFn.constName?)
        if heads.contains (m'.getAppFn.constName?.getD `_) then
          if let some (m2, h) ← g.withContext (normAction m') then
            g ← g.withContext (step1 g ``run_congr_bind #[none, none, m', m2, h, f, σ, r]); continue
      -- stepwise: only closed actions go to the kernel (symbolic ones can take minutes there)
      if !m'.containsConst (· == ``Airbender.resetState) && (wholeRest || !m'.hasFVar) then
       if let some (v, pf) ← g.withContext (oracleValue m') then
        let hm ← g.withContext (mkAppM ``oracle_run #[hs, m', v, pf])
        g ← g.withContext (step1 g ``run_bind_ok #[none, none, m', f, σ, v, r, hm]); continue
      if let some m'' ← delta? m' (fun _ => true) then
        let M' := mkAppN M.getAppFn (M.getAppArgs.set! 4 m'')
        g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runSail #[M', σ]) r)); continue
      return (g, hs, "stopped at an action")
    if let some M' ← delta? M (fun _ => true) then
      g ← g.replaceTargetDefEq (← g.withContext (mkEq (← mkAppM ``runSail #[M', σ]) r)); continue
    return (g, hs, "stopped")
  return (g, hs, "out of fuel")

def sailRun (hs : Syntax) (side : Option Syntax) (lemmas : Array Syntax := #[]) (wholeRest : Bool := true) :
    TacticM Unit := withMainContext do
  let hs ← elabTerm hs none
  let lemmas ← lemmas.mapM fun l => elabTerm l none
  oracleMs.set 0; oracleCalls.set 0
  let t0 ← IO.monoMsNow
  let (g, _, msg) ← sailRunLoop side lemmas (← getMainGoal) hs 2000 wholeRest
  logInfo m!"sail_run: {(← IO.monoMsNow) - t0} ms total, {← oracleCalls.get} kernel attempts taking {← oracleMs.get} ms"
  replaceMainGoal [g]
  logInfo m!"sail_run: {msg}"

syntax (name := sailRunUsing) "sail_run " term " using " tactic : tactic
elab_rules : tactic
  | `(tactic| sail_run $hs using $tac) => sailRun hs (some tac)
elab "sail_run " hs:term : tactic => sailRun hs none
/-- Like `sail_run … with […]`, but never evaluates the whole rest in the kernel (only single closed actions). -/
syntax (name := sailRunStepwise) "sail_run " term " using " tactic " with " "[" term,* "]" " stepwise" : tactic
elab_rules : tactic
  | `(tactic| sail_run $hs using $tac with [$ls,*] stepwise) => sailRun hs (some tac) ls.getElems false
syntax (name := sailRunWith) "sail_run " term " using " tactic " with " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| sail_run $hs using $tac with [$ls,*]) => sailRun hs (some tac) ls.getElems

end Slop.Equiv
