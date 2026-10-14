import Lean

/-! `kernel_rfl`: close `a = b` with `Eq.refl a`, checked ONLY by the Lean kernel (the elaborator's
definitional-equality check is skipped; it is far slower on the generated Sail model). Soundness is
unaffected: the kernel checks the auxiliary theorem like any other declaration. Unlike `decide +kernel`
it works on goals with free variables, as long as reduction never needs to inspect them. -/

open Lean Meta Elab Tactic

/-- `proof : ty` as an auxiliary theorem, kernel-checked now (not in the background), so a failure is an
exception the caller can catch. -/
def mkAuxTheoremNow (ty proof : Expr) : MetaM Expr :=
  withOptions (fun o => Elab.async.set (maxRecDepth.set o 1000000) false) (mkAuxTheorem ty proof)

elab "kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := ty.eq? | throwError "kernel_rfl: goal is not an equality"
  let u ← getLevel α
  g.assign (← mkAuxTheorem ty (mkApp2 (mkConst ``Eq.refl [u]) α lhs))
  replaceMainGoal []

example (n : Nat) : (fun x => x + 0) n = n := by kernel_rfl
