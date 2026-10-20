import Airbender.Proofs.ShiftBinop.BinaryResults

namespace Airbender.ShiftBinop
open Arithmetic Verification Trace
set_option autoImplicit false

/-- Native XOR/OR/AND, including immediate forms, force bounded RV32 operands,
    the exact bitwise result and the actual decoded x0-masked write. -/
theorem native_decoded_binary_result {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      decoderQuery w = entry.query ∧ Routing w entry ∧
      ∀ kind, entry.data.family = binaryOperation kind →
        BinaryResult w kind (decide (entry.data.rd = 0)) :=
  Proofs.fetched_binary_result image holds member

end Airbender.ShiftBinop
