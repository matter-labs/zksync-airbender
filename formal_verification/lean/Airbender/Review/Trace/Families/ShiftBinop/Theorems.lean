import Airbender.Proofs.Trace.Families.ShiftBinop.Results

namespace Airbender.ShiftBinop
open Arithmetic Trace
set_option autoImplicit false

/-- Public code, actual Sail seeds/PC and native matching derive exact ordinary
    shift/binop numerical results and actual x0-masked writes. Original Sail
    register/cell and instruction execution remain separate connections. -/
theorem public_native_results {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
      selectedWord row.assignment = Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) ∧
      writtenWord row.assignment = if entry.data.rd = 0 then ⟨0,0⟩ else Word.ofBitVec
        (entry.data.family.result (left row.assignment) (right row.assignment)) :=
  Proofs.initialized_results image inputs accepted decoded

end Airbender.ShiftBinop
