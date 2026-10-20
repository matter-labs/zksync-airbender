import Airbender.Proofs.SubwordMemory.StorePlace

namespace Airbender.Verification.SubwordStorePlace
set_option autoImplicit false

/-- Exact native written-value placement from lookup membership.
    Preselection, accepted store constraints and original Sail execution are separate. -/
theorem native_values {key output unused : ZMod mersenne31Modulus}
    (member : table.Contains #[] #v[key, output, unused]) :
    key.val < 2097152 ∧ output = (placed key.val : Nat) ∧ unused = 0 ∧ output.val < 65536 := by
  exact Airbender.SubwordMemory.StorePlaceProofs.store_place_values member

end Airbender.Verification.SubwordStorePlace
