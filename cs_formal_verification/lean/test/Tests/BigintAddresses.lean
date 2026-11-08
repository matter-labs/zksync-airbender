module
public import Tests.BigintMultiplication

@[expose] public section

namespace Tests.BigintAddresses
open Airbender
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem unalignedPointerRejected (w : Nat → ZMod babyBearModulus)
    (unaligned : (w 3).val % 32 ≠ 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Bigint.importedConstraints Bigint.setupTable) := by
  intro row
  exact unaligned (Bigint.Addresses.Proofs.pointer_alignment (by decide) (by decide) row).1

def boundaryRow : Nat → ZMod babyBearModulus := fun column =>
  if column = 3 ∨ column = 37 then 65504
  else if column = 4 ∨ column = 38 then 65535
  else 0

/-- Last aligned block of the 32-bit address space: all eight addresses stay
    in the block, including the final word at 2^32 - 4. Address projection only. -/
theorem boundaryAddresses (i : Fin 16) :
    (Bigint.importedConstraintsIndirectPorts[i].address boundaryRow).toNat =
      2 ^ 32 - 32 + 4 * (i.val % 8) := by
  fin_cases i <;> decide

end Tests.BigintAddresses
