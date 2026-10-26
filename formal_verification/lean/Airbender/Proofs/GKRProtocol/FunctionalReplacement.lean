import Airbender.Proofs.GKRProtocol.FunctionalBindings

namespace Airbender.Compiler
set_option warningAsError true

theorem FunctionalStep.Valid.replace {isBase : GKRAddress → Bool} {known : List GKRAddress}
    {before after : FunctionalStep} (valid : before.Valid isBase known)
    (outputs : after.outputs = before.outputs) (inputs : after.inputs = before.inputs) :
    after.Valid isBase known := by
  refine ⟨outputs.symm ▸ valid.unique, ?_, ?_⟩
  · simpa only [outputs] using valid.fresh
  · simpa only [inputs] using valid.inputs

theorem FunctionalProgram.Valid.replace {isBase : GKRAddress → Bool} {known : List GKRAddress}
    {before after : FunctionalProgram} (valid : before.Valid isBase known)
    (same : List.Forall₂ (fun first second => second.outputs = first.outputs ∧ second.inputs = first.inputs) before after) :
    after.Valid isBase known := by
  induction valid generalizing after with
  | nil => cases same; exact .nil
  | @cons known step rest current remaining proof =>
    cases same with
    | cons shape tail =>
      exact .cons (current.replace shape.1 shape.2) (shape.1.symm ▸ proof tail)

end Airbender.Compiler
