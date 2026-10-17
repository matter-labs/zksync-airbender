import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.AddSub.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 37 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 12 := rfl

end Airbender.AddSub.Proofs
