import Airbender.Proofs.ShiftBinop.Routing

namespace Airbender.ShiftBinop
open Arithmetic Trace
set_option autoImplicit false

/-- Public original bytes/decoding and native acceptance determine all four
    table tags, the selected operand limbs and disabled ordinary delegation. -/
theorem native_decoded_routing {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry :=
  Proofs.fetched_routing image holds member

end Airbender.ShiftBinop
