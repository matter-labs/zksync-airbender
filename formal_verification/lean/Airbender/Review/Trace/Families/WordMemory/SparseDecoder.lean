import Airbender.Proofs.Trace.Families.WordMemory.SparseDecoder
import Airbender.Proofs.Mersenne31
import Airbender.Proofs.WordMemory.NativeSparseSetup

namespace Airbender.WordMemory
open Trace

/-- Actual public words may include unsupported holes. Native equations reject
    hole/tail lookups before original Sail bytes and decoding are recovered. -/
theorem sparse_public_decoder_soundness {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : SparseDecoderSetup WordMemoryFamily} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : SparseDecoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ row.decoderQuery = entry.query :=
  Proofs.sparse_decoded_sources (by decide) image accepted decoded

/-- The pinned native export has a real unsupported interior word. Actual row
    constraints and exported membership recover original public Sail evidence. -/
theorem exported_sparse_decoder_soundness {rom : Verification.WordROM}
    {row : Row mersenne31Modulus WordMemoryFamily}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom))
    (member : ∃ i : Fin 1048576, row.decoderQuery = NativeSparse.holesDecoder.row i) :
    ∃ entry ∈ NativeSparse.setup.program,
      entry.SourceWith NativeSparse.before decoderFields ∧ row.decoderQuery = entry.query :=
  Proofs.sparse_exported_source constraints member

end Airbender.WordMemory
