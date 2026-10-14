import Lean
import Slop.Sail.KernelRfl

/-! `sym_step`: symbolic execution by the kernel.

Goal `lhs = rhs`. Repeatedly: reduce `lhs` with the kernel's `whnf`; if the result is kernel-defeq to `rhs`, done.
Otherwise the reduction is stuck on a recursor whose major premise depends on free variables; we find the
outermost `Bool`-valued stuck major premise `c`, prove `c = true` (or `c = false`) with the given discharger,
substitute it into the residual term, and continue. Every equation in the chain is checked by the kernel
(`lhs = residual` by `Eq.refl` in an auxiliary theorem) or is a `congrArg` of a proved fact. -/

open Lean Meta Elab Tactic

namespace Slop.SymStep

def dbg (msg : String) : MetaM Unit := do
  if (← IO.getEnv "SYMSTEP_DEBUG").isSome then
    IO.eprintln s!"[{← IO.monoMsNow}] {msg}"

def kwhnf (e : Expr) : MetaM Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => pure r
  | .error ex => throwError "sym_step: kernel whnf failed: {ex.toMessageData {}}"

def kdefeq (a b : Expr) : MetaM Bool := do
  match Kernel.isDefEq (← getEnv) (← getLCtx) a b with
  | .ok r => pure r
  | .error _ => pure false

/-- The outermost `Bool`-typed stuck major premise `c` along the chain of stuck recursors of `e` (in whnf),
together with `e*`: `e` with the majors on the path replaced by their whnf, so that `e* ≡ e` and `c` occurs in
`e*` syntactically. -/
partial def findStuck (e : Expr) (fuel : Nat := 200) : MetaM (Option (Expr × Expr)) := do
  if fuel = 0 then return none
  let e := e.headBeta
  if let .proj sn i x := e then
    let some (c, x') ← findStuck (← kwhnf x) (fuel - 1) | return none
    return some (c, .proj sn i x')
  let .const n _ := e.getAppFn | return none
  let some (.recInfo rv) := (← getEnv).find? n | return none
  let args := e.getAppArgs
  let majorIdx := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
  if h : majorIdx < args.size then
    let major := args[majorIdx]
    if n == ``Bool.rec || n == ``Bool.casesOn then return some (major, e)
    let some (c, major') ← findStuck (← kwhnf major) (fuel - 1) | return none
    return some (c, mkAppN e.getAppFn (args.set majorIdx major'))
  else return none

/-- Core-library constants (Init/Std): arithmetic and comparisons that we keep folded on symbolic data. -/
def isBarrier (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n | return false
  let mod := env.header.moduleNames[idx.toNat]!
  return mod.getRoot == `Init || mod.getRoot == `Std

/-- For `f` applied to `n` arguments: which arguments to leave alone (types, proofs, instances).
Computed from `f`'s type only, never from the (possibly huge) arguments. -/
def skipMask (f : Expr) (n : Nat) : MetaM (Array Bool) := do
  try
    forallBoundedTelescope (← inferType f) n fun xs _ => xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then return true
      let t ← whnfD d.type
      if t.isSort then return true
      return (← isProp d.type)
  catch _ => return #[]

/-- Full kernel normalisation of a closed term (proofs and types are left alone). -/
partial def kernelNormClosed (e : Expr) : MetaM Expr := do
  let e' ← kwhnf e
  if e'.isApp then
    let f := e'.getAppFn
    let args := e'.getAppArgs
    let mask ← skipMask f args.size
    let mut out := #[]
    for h : i in [0:args.size] do
      if mask.getD i false then out := out.push args[i] else out := out.push (← kernelNormClosed args[i])
    return mkAppN f out
  else return e'

/-- Simplify `e` for the discharger: closed subterms are normalised by the kernel; open terms are unfolded
step by step (Meta `whnfCore` + one delta step at a time), stopping at core-library functions (`Init`/`Std`:
arithmetic, comparisons, `ite`, ...) whose arguments are then cleaned recursively. -/
partial def clean (e : Expr) (fuel : Nat := 10000) : MetaM Expr := do
  if fuel = 0 then return e
  if !e.hasFVar then return ← kernelNormClosed e
  let e ← whnfCore e
  if let .proj sn i x := e then
    let e' := Expr.proj sn i (← clean x (fuel - 1))
    let e'' ← whnfCore e'
    return ← if e'' == e' then pure e' else clean e'' (fuel - 1)
  if let .const n _ := e.getAppFn then
    unless ← isBarrier n do
      if let some e' ← unfoldDefinition? e then return ← clean e' (fuel - 1)
  let r ← cleanArgs e (fuel - 1)
  let r' ← whnfCore r
  if r' == r then return r else clean r' (fuel - 1)
where
  cleanArgs (e : Expr) (fuel : Nat) : MetaM Expr := do
    let f := e.getAppFn
    let args := e.getAppArgs
    if args.isEmpty then return e
    let mask ← skipMask f args.size
    let mut out := #[]
    for h : i in [0:args.size] do
      if mask.getD i false then out := out.push args[i] else out := out.push (← clean args[i] fuel)
    return mkAppN f out

/-- `a = b` proved by `Eq.refl a`, checked only by the kernel (auxiliary theorem). -/
def kernelEq (a b : Expr) : MetaM Expr := do
  let α ← inferType a
  let u ← getLevel α
  mkAuxTheorem (mkApp3 (mkConst ``Eq [u]) α a b) (mkApp2 (mkConst ``Eq.refl [u]) α a)

/-- Prove `c = v` (v a Bool literal) with tactic `tac`; `none` if it fails. -/
def proveBool (c : Expr) (v : Bool) (tac : Syntax) : TacticM (Option Expr) := do
  let goalTy ← mkEq c (toExpr v)
  let mv ← mkFreshExprSyntheticOpaqueMVar goalTy
  let saved ← saveState
  let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
  try
    let gs ← Tactic.run mv.mvarId! (withoutRecover (evalTactic tac))
    let pf ← instantiateMVars mv
    let errsAfter := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    if gs.isEmpty && !pf.hasSorry && errsAfter == errsBefore then return some pf
    saved.restore
    return none
  catch _ =>
    saved.restore
    return none

def run (tac : Syntax) (maxSteps : Nat) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, rhs) := ty.eq? | throwError "sym_step: goal is not an equality"
  let u ← getLevel α
  let mut cur := lhs
  let mut prf := mkApp2 (mkConst ``Eq.refl [u]) α lhs   -- : lhs = cur
  for i in [0:maxSteps] do
    dbg s!"sym_step: step {i}: whnf"
    let r ← kwhnf cur
    dbg s!"sym_step: step {i}: whnf done"
    if ← kdefeq r rhs then
      let last ← kernelEq cur rhs
      g.assign (← mkEqTrans prf last)
      replaceMainGoal []
      return
    let some (c, rs) ← findStuck r
      | throwError "sym_step: step {i}: not stuck on a Bool condition, but not equal to the goal's right-hand side:{indentExpr r}"
    dbg s!"sym_step: step {i}: stuck"
    let c' ← clean c
    dbg s!"sym_step: cleaned to "
    dbg "cleaned"
    let hcc ← kernelEq c c'                         -- c = c'
    dbg "c = c' checked"
    let (v, hc') ← match ← proveBool c' true tac with
      | some h => pure (true, h)
      | none => match ← proveBool c' false tac with
        | some h => pure (false, h)
        | none => throwError "sym_step: step {i}: cannot decide{indentExpr c'}"
    dbg s!"decided {v}"
    let hc ← mkEqTrans hcc hc'
    let hr ← kernelEq cur rs                        -- cur = rs
    dbg "cur = rs checked"
    let body ← kabstract rs c
    dbg s!"sym_step: abstracted"
    unless body.hasLooseBVars do throwError "sym_step: could not abstract{indentExpr c}"
    let motive := mkLambda `b .default (mkConst ``Bool) body
    let r' := body.instantiate1 (toExpr v)
    let hcr := mkAppN (mkConst ``congrArg [1, u]) #[mkConst ``Bool, α, c, toExpr v, motive, hc]  -- rs = r'
    prf ← mkEqTrans prf (← mkEqTrans hr hcr)
    cur := r'
    trace[Meta.debug] "sym_step: {c} = {v}"
  throwError "sym_step: no result after {maxSteps} steps"

end Slop.SymStep

/-- `sym_step using tac`: symbolic execution by the kernel; stuck `Bool` conditions are discharged by `tac`
(which must prove goals of the form `c = true` or `c = false`). -/
elab "sym_step" " using " tac:tacticSeq : tactic => Slop.SymStep.run tac 200
