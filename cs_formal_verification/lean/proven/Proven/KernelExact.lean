module
public import Lean
public meta import Lean

public meta section

/-! Infer a proof term once. The kernel checks its complete type against the enclosing theorem.
This avoids duplicate elaborator normalization of large concrete artifact types. -/

open Lean Meta Elab Tactic in
elab "kernel_exact " proof:term : tactic => withMainContext do
  let value ← Term.elabTerm proof none
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  (← getMainGoal).assign value
  replaceMainGoal []
