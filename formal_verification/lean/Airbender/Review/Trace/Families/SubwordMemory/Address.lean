import Airbender.Proofs.Trace.Families.SubwordMemory.Address

namespace Airbender.SubwordMemory
open Arithmetic Trace
set_option autoImplicit false

/-- Public initialization and original decoding derive RV32 effective addresses,
    offsets and actual aligned RAM/ROM-shadow port words from native acceptance.
    No per-row read, range, address, flag or desired-effect premise is supplied. -/
theorem public_native_addresses {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment :=
  Proofs.image_native_addresses image inputs accepted decoded

end Airbender.SubwordMemory
