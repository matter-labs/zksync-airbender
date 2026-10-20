import Airbender.Proofs.SubwordMemory.Decoder

namespace Airbender.SubwordMemory
open Verification Trace
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
  {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {count logCapacity : Nat}

theorem native_fetched_fields
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧ DecodedFields w entry :=
  Proofs.fetched_fields image holds member

theorem native_fetched_load_writes
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (member : setup.table.Contains #[] (decoderQuery w)) (load : w 12 = 0) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      DecodedFields w entry ∧ DecodedLoadWrites w entry :=
  Proofs.fetched_load_writes image holds member load

end Airbender.SubwordMemory
