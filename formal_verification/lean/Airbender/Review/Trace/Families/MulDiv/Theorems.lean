import Airbender.Proofs.Trace.Families.MulDiv.Results

namespace Airbender.MulDiv
open Arithmetic Trace

/-- Actual public Sail bytes/decoding, seed reads and native matching derive
    all numerical interfaces for every unsigned row, including discarded x0
    writes. Original Sail instruction execution/retirement is a later connection. -/
theorem public_native_results {trace : Data mersenne31Modulus MulDivFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {cells : List Cell} {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query ∧
      (selectedWord row.assignment).value = entry.data.family.result
        (left row.assignment) (right row.assignment) ∧
      (writtenWord row.assignment).value = if entry.data.rd = 0 then 0 else
        entry.data.family.result (left row.assignment) (right row.assignment) :=
  Proofs.initialized_results image inputs accepted decoded

end Airbender.MulDiv
