import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.MulDiv.Proofs

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 49 := rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 20 := rfl

theorem setup_columns : importedConstraintsSetupColumns =
    (⟨16777216,16,0,1,2,1,6,1048576,65536⟩ : Verification.SetupColumns) := rfl

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5,6,7,8,#v[9,10],11,12⟩ : Trace.DecoderColumns) := rfl

end Airbender.MulDiv.Proofs
