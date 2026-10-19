import Airbender.Proofs.MulDiv.Results

namespace Airbender.MulDiv
open Arithmetic Verification

/-- Native unsigned arithmetic, including zero divisors and actual discarded
    writes. Packed decoding, destination-zero identification and the register
    input bound are explicit row interfaces; public decoding, initialized
    history and original Sail execution are subsequent connections. -/
theorem native_unsigned_result (w : Nat → ZMod mersenne31Modulus)
    (operation : Operation) (discarded : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : (w 12).val = operation.nativeMask)
    (leftBound : (left w).Bounded)
    (zeroFlag : w 8 = if discarded then 1 else 0) :
    (selectedWord w).value = operation.result (left w) (right w) ∧
      (writtenWord w).value = if discarded then 0 else operation.result (left w) (right w) :=
  Proofs.native_masked_result holds operation discarded selected leftBound zeroFlag

end Airbender.MulDiv
