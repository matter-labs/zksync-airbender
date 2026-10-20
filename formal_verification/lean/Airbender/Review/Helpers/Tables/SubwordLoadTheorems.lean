import Airbender.Proofs.SubwordMemory.Load

namespace Airbender.Verification.SubwordLoad
set_option autoImplicit false

/-- Exact native signed/unsigned load-data semantics and canonical output bounds.
    The preselected limb is encoded in the key; full circuit/Sail execution is separate. -/
theorem native_values {key low high : ZMod mersenne31Modulus}
    (member : table.Contains #[] #v[key, low, high]) :
    key.val < 2097152 ∧ low = ((limbs key.val).1 : Nat) ∧
      high = ((limbs key.val).2 : Nat) ∧ low.val < 65536 ∧ high.val < 65536 := by
  exact Airbender.SubwordMemory.LoadProofs.load_values member

end Airbender.Verification.SubwordLoad
