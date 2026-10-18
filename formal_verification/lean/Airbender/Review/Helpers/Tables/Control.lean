import Airbender.Proofs.JumpBranchSlt.ControlTables

namespace Airbender.Verification

/-- Cleanup membership is exactly membership in the complete actual tagged native export. -/
theorem native_jump_cleanup (query : Vector (ZMod mersenne31Modulus) 3) :
    jumpCleanupTable.Contains #[] query ↔ ∃ i : Fin 65536,
      query.push 17 = JumpBranchSlt.Native.controlCleanup.row i :=
  JumpBranchSlt.Proofs.cleanup_lookup query

/-- Conditional membership retains both native keys and the actual result/tag. -/
theorem native_conditional_control (query : Vector (ZMod mersenne31Modulus) 3) :
    conditionalControlTable.Contains #[] query ↔ ∃ i : Fin 128,
      query.push 43 = JumpBranchSlt.Native.controlConditional.row i :=
  JumpBranchSlt.Proofs.conditional_lookup query

end Airbender.Verification
