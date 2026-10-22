import Airbender.Proofs.SerializedInverse

namespace Airbender.Blake2G.Proofs
set_option Elab.async false

/-- This serialized inverse belongs to BabyBear. A different field needs its
    own imported coefficients, even though the arithmetic lemmas are generic. -/
theorem serialized_field {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p) : p = babyBearModulus :=
  SerializedInverse.scale64_field compatible

theorem inverse256 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p) : SerializedInverse.Scale256 p :=
  SerializedInverse.scale64_scale256 compatible

end Airbender.Blake2G.Proofs
