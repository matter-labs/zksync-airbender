import Airbender.Proofs.SubwordMemory.Offset

namespace Airbender.Verification.SubwordOffset
set_option autoImplicit false

/-- Exact native v2 offset-table meaning. The mask keeps its trap bit and the
    explicit x0 load exception; full circuit acceptance/execution is separate. -/
theorem native_values {key offset mask : ZMod mersenne31Modulus}
    (member : table.Contains #[] #v[key, offset, mask]) :
    key.val < 2097152 ∧ offset = (key.val % 4 : Nat) ∧ mask = (SubwordOffset.mask key.val : Nat) := by
  exact Airbender.SubwordMemory.Proofs.offset_values member

end Airbender.Verification.SubwordOffset
