import Lean

/-! `#kernel_eval e`: debug command printing the normal form of a closed term computed with the kernel's
`whnf` (much faster than `#reduce` on the generated Sail model). Not used in proofs. -/

open Lean Elab Command Meta

partial def kernelNorm (e : Expr) : MetaM Expr := do
  let env ← getEnv
  let e ← match Kernel.whnf env {} e with
    | .ok e => pure e
    | .error ex => throwError "kernel whnf failed: {ex.toMessageData {}}"
  if e.isApp then
    let args ← e.getAppArgs.mapM fun a => do
      if (← isProof a) || (← isType a) then pure a else kernelNorm a
    return mkAppN e.getAppFn args
  else return e

elab "#kernel_eval " t:term : command => liftTermElabM do
  let e ← instantiateMVars (← Term.elabTerm t none)
  Term.synthesizeSyntheticMVarsNoPostponing
  logInfo m!"{← kernelNorm (← instantiateMVars e)}"
