module
public import Proven.ISA.ValidUse

@[expose] public section
namespace RV.ValidUse
set_option warningAsError true

/-- The valid-input delegation result equals its independent reference function. -/
theorem bigint_reference : BigintReferenceClaim := RV.ValidUse.Proofs.bigint_reference

/-- The valid-input delegation result equals its independent reference function. -/
theorem g_reference : GReferenceClaim := RV.ValidUse.Proofs.g_reference

/-- The valid-input delegation result equals its independent reference function. -/
theorem round_reference : RoundReferenceClaim := RV.ValidUse.Proofs.round_reference

/-- The valid-input delegation result equals its independent reference function. -/
theorem hash_reference : HashReferenceClaim := RV.ValidUse.Proofs.hash_reference

/-- The valid-input delegation result equals its independent reference function. -/
theorem split_keccak_reference : SplitKeccakReferenceClaim := RV.ValidUse.Proofs.split_keccak_reference

/-- The valid-input delegation result equals its independent reference function. -/
theorem special5_reference : Special5ReferenceClaim := RV.ValidUse.Proofs.special5_reference

end RV.ValidUse
