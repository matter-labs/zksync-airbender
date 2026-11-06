import Lean

/-! `deferred_rfl`: close `a = b` with `Eq.refl a`, skipping the elaborator's definitional check; the kernel
checks the equation together with the enclosing declaration (lean-strategies §2.4: kernel evaluation of closed
data is fast, the elaborator's check of the same unfolding is far slower). Unlike `kernel_rfl`
(`Slop.Sail.Configured`), no auxiliary theorem is made, so the goals of one declaration share the kernel's
cache. A false equation is rejected by the kernel check of that declaration. -/

open Lean Meta Elab Tactic in
elab "deferred_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := ty.eq? | throwError "deferred_rfl: goal is not an equality"
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []
