module
public import Lean
public meta import Lean

public meta section

/-! `kernel_rfl`: close `a = b` with `Eq.refl a`, skipping the elaborator's definitional check; the kernel checks
the equation together with the enclosing declaration (lean-strategies §2.4: kernel evaluation of closed data is
fast, the elaborator's check of the same unfolding is far slower, e.g. on the generated Sail model). No auxiliary
theorem is made, so the goals of one declaration share the kernel's cache. A false equation is rejected by the
kernel check of that declaration (not by the tactic: inside `first | ...` it does not fall through). -/

open Lean Meta Elab Tactic in
elab "kernel_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, _) := ty.eq? | throwError "kernel_rfl: goal is not an equality"
  let u ← getLevel α
  g.assign (mkApp2 (mkConst ``Eq.refl [u]) α lhs)
  replaceMainGoal []
