import Airbender.Proofs.SubwordMemory.StoreClear

namespace Airbender.Verification.SubwordStoreClear
set_option autoImplicit false

/-- Exact native original-RAM-limb clearing from lookup membership.
    Preselection, accepted store constraints and original Sail execution are separate. -/
theorem native_values {key output unused : ZMod mersenne31Modulus}
    (member : table.Contains #[] #v[key, output, unused]) :
    key.val < 2097152 ∧ output = (cleared key.val : Nat) ∧ unused = 0 ∧ output.val < 65536 := by
  exact Airbender.SubwordMemory.StoreClearProofs.store_clear_values member

end Airbender.Verification.SubwordStoreClear
