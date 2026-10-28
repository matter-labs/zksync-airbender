import Airbender.Review.Circuits.Keccak.SplitColumnParity
import Airbender.Review.Circuits.Keccak.SplitThetaRho
import Airbender.Review.Circuits.Keccak.SplitChi5

namespace Airbender.Keccak.Split.Proofs

/-- The emitted native timestamp query arrays and grouped metadata retain
the exact sizes of the three split compiled artifacts. -/
theorem column_parity_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ColumnParity.importedConstraintsTimestampLookups (p := p)).length = 30 := by rfl

theorem theta_rho_timestamp_queries {p : Nat} [Fact p.Prime] :
    (ThetaRho.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem chi5_timestamp_queries {p : Nat} [Fact p.Prime] :
    (Chi5.importedConstraintsTimestampLookups (p := p)).length = 2 := by rfl

theorem theta_rho_timestamp_groups :
    ThetaRho.importedConstraintsTimestampGroups.size = 4 := by rfl

theorem chi5_timestamp_groups :
    Chi5.importedConstraintsTimestampGroups.size = 6 := by rfl

end Airbender.Keccak.Split.Proofs
