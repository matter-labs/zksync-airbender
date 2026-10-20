import Airbender.Proofs.ShiftBinop.ShiftContributions

namespace Airbender.ShiftBinop
open Arithmetic Verification Trace
set_option autoImplicit false

/-- Public decoding and native acceptance derive truncation, all three exact
    packed-key contributions and actual selected-word assembly for SLL/SRL/SRA. -/
theorem native_decoded_shift_contributions {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry ∧
      ∀ kind, entry.data.family = kind.operation → ShiftContributions w kind :=
  Proofs.fetched_shift_contributions image holds member

end Airbender.ShiftBinop
