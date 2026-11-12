module
public import Proven.Blake2Round.Mask.Satisfiable

@[expose] public section
namespace Airbender.Blake2Round.Mask

/-- Every accepted Boolean-mask row computes its full native round reference. -/
theorem soundness : SoundnessClaim := Proofs.soundness

/-- The existing verified first round meets every native row premise. -/
theorem satisfiable : SatisfiableClaim := Proofs.satisfiable

end Airbender.Blake2Round.Mask
