module
public import Proven.Blake2Round.Mask.Satisfiable
public import Proven.Blake2Round.Mask.RVEffectChoice

@[expose] public section
namespace Airbender.Blake2Round.Mask

/-- Every accepted Boolean-mask row computes its full native round reference. -/
theorem soundness : SoundnessClaim := Proofs.soundness

/-- An active zero-mask row meets every native row premise. -/
theorem satisfiable : SatisfiableClaim := Proofs.satisfiable

end Airbender.Blake2Round.Mask

namespace RV.Delegation

/-- A one-hot mask in the selected schedule gives the reference SIGMA round effect. -/
theorem blake_round_one_hot : BlakeRoundOneHotClaim :=
  Airbender.Blake2Round.Mask.Proofs.onehot_reference

/-- Round zero supplies the separate one-hot control witness. -/
theorem blake_round_one_hot_satisfiable : BlakeRoundOneHotSatisfiableClaim :=
  Airbender.Blake2Round.Mask.Proofs.onehot_reference_satisfiable

end RV.Delegation
