import Airbender.Proofs.ShiftBinop.NativeSetup

namespace Airbender.ShiftBinop
open Trace NativeSetup

/-- The actual ordinary native decoder export equals independently read and
    originally decoded public Sail setup, across the complete native capacity.
    Dynamic lookup constraints and custom CSR semantics remain separate. -/
theorem exported_decoder_fidelity :
    sparseDecoderSetupImage before 25 20 = some setup ∧
    ∀ i : Fin 1048576, nativeDecoder.row (p := mersenne31Modulus) i = setup.row i :=
  ⟨Proofs.native_fixture_image,Proofs.native_exported_rows⟩

end Airbender.ShiftBinop
