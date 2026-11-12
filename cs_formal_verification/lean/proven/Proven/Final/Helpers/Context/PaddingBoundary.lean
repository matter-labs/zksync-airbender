module
public import Human.Helpers.Context.PaddingBoundary.Theorems
public import Proven.Trace.PaddingBoundary

@[expose] public section
namespace Airbender.PaddingBoundary
set_option warningAsError true

/-- Each Boolean tuple contribution is the native mask gate. -/
theorem contribution_soundness : ContributionSoundnessClaim := Proofs.evaluate_contribution

/-- Each row product uses the same native mask gate. -/
theorem product_soundness : ProductSoundnessClaim := Proofs.evaluate_group

/-- Full masked tuple closure derives active-row acceptance. -/
theorem projection : ProjectionClaim := fun _ accepted => Proofs.projected_acceptance accepted

end Airbender.PaddingBoundary
