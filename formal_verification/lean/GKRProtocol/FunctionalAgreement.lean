import GKRProtocol.FunctionalBindings

namespace Airbender.Compiler
set_option warningAsError true

theorem FunctionalStep.output_agrees {R : Type} [CommRing R] (step : FunctionalStep)
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R) (gamma : R)
    (left right : GKRAddress → R)
    (leftHolds : step.Holds hom challenges gamma left)
    (rightHolds : step.Holds hom challenges gamma right)
    (inputs : ∀ address ∈ step.inputs, left address = right address)
    (address : GKRAddress) (output : address ∈ step.outputs) : left address = right address := by
  obtain ⟨entry, member, same⟩ := List.mem_map.mp output
  subst address
  exact (leftHolds entry member).trans ((entry.2.value_congr hom challenges gamma left right
    (fun input included => inputs input (List.mem_flatMap.mpr ⟨entry, member, included⟩))).trans
      (rightHolds entry member).symm)

end Airbender.Compiler
