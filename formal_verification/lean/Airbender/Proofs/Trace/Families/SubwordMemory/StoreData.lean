import Airbender.Proofs.Trace.Families.SubwordMemory.LoadData
import Airbender.Proofs.SubwordMemory.StoreData

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Verification
set_option autoImplicit false

/-- The actual third native read is bounded by initialized history, including
    the old RAM word for stores. No old-data value or range is supplied. -/
theorem old_bound_of_reads {trace : Data mersenne31Modulus SubwordMemoryFamily}
    (ranges : ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (readToken row.assignment port).word.Bounded)
    (row : Row mersenne31Modulus SubwordMemoryFamily) (member : row ∈ trace.rows) :
    (oldWord row.assignment).Bounded := by
  have port : importedConstraintsMemoryPorts[2] ∈ row.ports := by
    cases row with
    | mk family w =>
      cases family
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts]
  have data := ranges row member _ port
  simpa [Trace.Proofs.read_word,importedConstraintsMemoryPorts,
    WordColumns.evaluate,oldWord] using data

/-- One original public state supplies initialization and sparse decoding.
    Actual initialized source/old reads discharge every local store interface. -/
theorem image_native_stores {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment ∧ NativeStoreEffects row.assignment entry := by
  have ranges := (image_value_bounds image inputs accepted decoded).1
  have addresses := image_native_addresses image inputs accepted decoded
  intro row present
  obtain ⟨entry,member,source,fields,geometry⟩ := addresses row present
  have sourceBound := data_bound_of_reads ranges row present
  have oldBound := old_bound_of_reads ranges row present
  have native := accepted.constraints row present
  cases row with
  | mk family w =>
    cases family
    exact ⟨entry,member,source,fields,geometry,entry_store_effect native fields sourceBound oldBound⟩

end Airbender.SubwordMemory.Proofs
