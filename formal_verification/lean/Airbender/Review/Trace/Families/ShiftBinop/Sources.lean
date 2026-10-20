import Airbender.Proofs.Trace.Families.ShiftBinop.Sources

namespace Airbender.ShiftBinop
open Trace
set_option autoImplicit false

/-- Public initialization, native matching and actual public decoding derive
    bounded source reads and canonical packed shift keys, including x0 writes.
    No per-row range, desired source/key or expected selected result is assumed. -/
theorem public_shift_sources {trace : Data mersenne31Modulus ShiftBinopFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (row : Row mersenne31Modulus ShiftBinopFamily)
    (present : row ∈ trace.rows) :
    ∃ entry ∈ setup.program, entry.SourceWith before decoderFields ∧
      row.decoderQuery = entry.query ∧
      ∀ kind, entry.data.family = kind.operation → ShiftSourceBinding row.assignment kind :=
  Proofs.image_shift_sources image inputs accepted decoded row present

end Airbender.ShiftBinop
