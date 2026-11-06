import Airbender.Review.Circuits.ReducedMachine.Tables.Native
import Airbender.Review.Helpers.Tables.NativeBinaryRows

namespace Airbender.ReducedMachine.NativeBitwiseDataProofs
open NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Exact independently emitted native data identity, not an assumption. -/
theorem xor_data : dataT4 = NativeBinary.dataXor := by rfl

theorem or_data : dataT6 = NativeBinary.dataOr := by rfl

theorem and_data : dataT7 = NativeBinary.dataAnd := by rfl

end Airbender.ReducedMachine.NativeBitwiseDataProofs
