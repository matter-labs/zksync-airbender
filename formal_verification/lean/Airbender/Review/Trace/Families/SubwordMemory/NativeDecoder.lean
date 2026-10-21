import Airbender.Proofs.SubwordMemory.NativeSetup

namespace Airbender.SubwordMemory
open Trace NativeSetup
set_option autoImplicit false

/-- Specific native exported decoder fidelity, retaining every supported row,
    unsupported slot and sentinel. General Rust/compiler refinement is separate. -/
theorem exported_decoder_fidelity :
    sparseDecoderSetupImage before 13 20 = some setup ∧
    ∀ i : Fin 1048576, nativeDecoder.row (p := mersenne31Modulus) i = setup.row i :=
  ⟨Proofs.native_fixture_image,Proofs.native_exported_rows⟩

end Airbender.SubwordMemory
