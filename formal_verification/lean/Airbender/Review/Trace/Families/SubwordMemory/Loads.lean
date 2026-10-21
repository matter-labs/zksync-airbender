import Airbender.Proofs.Trace.Families.SubwordMemory.LoadData

namespace Airbender.SubwordMemory
open Arithmetic Trace
set_option autoImplicit false

/-- Public initialization, original decoding and native acceptance derive
    byte/halfword Sail extension functions and actual masked writes. Native ROM
    indexing is exact; architectural ROM and original execution are separate. -/
theorem public_native_loads {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment ∧ NativeLoadEffects trace.rom row.assignment entry :=
  Proofs.image_native_loads image inputs accepted decoded

end Airbender.SubwordMemory
