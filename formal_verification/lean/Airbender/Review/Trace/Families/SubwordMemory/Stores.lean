import Airbender.Proofs.Trace.Families.SubwordMemory.StoreData

namespace Airbender.SubwordMemory
open Arithmetic Trace
set_option autoImplicit false

/-- Public initialization, original decoding and native acceptance derive every
    changed and preserved SB/SH byte. Original memory access/exception and
    instruction retirement remain separate from this data-effect claim. -/
theorem public_native_stores {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment ∧ NativeStoreEffects row.assignment entry :=
  Proofs.image_native_stores image inputs accepted decoded

end Airbender.SubwordMemory
