module
public import Proven.Blake2Round.Mask.RVEffectChoice

@[expose] public section
namespace RV.Delegation

/-- A one-hot mask in the selected schedule gives the reference SIGMA round effect. -/
theorem blake_round_one_hot : BlakeRoundOneHotClaim :=
  Airbender.Blake2Round.Mask.Proofs.onehot_reference

/-- Round zero supplies the separate one-hot control witness. -/
theorem blake_round_one_hot_satisfiable : BlakeRoundOneHotSatisfiableClaim :=
  Airbender.Blake2Round.Mask.Proofs.onehot_reference_satisfiable

end RV.Delegation
