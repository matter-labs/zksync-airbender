import Airbender.Proofs.Trace.Families.SubwordMemory.Address
import Airbender.Proofs.SubwordMemory.LoadData

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Verification
set_option autoImplicit false

/-- The actual second native read is bounded by initialized history, including
    its ROM-shadow and store-source interpretations. -/
theorem data_bound_of_reads {trace : Data mersenne31Modulus SubwordMemoryFamily}
    (ranges : ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (readToken row.assignment port).word.Bounded)
    (row : Row mersenne31Modulus SubwordMemoryFamily) (member : row ∈ trace.rows) :
    (dataWord row.assignment).Bounded := by
  have port : importedConstraintsMemoryPorts[1] ∈ row.ports := by
    cases row with
    | mk family w =>
      cases family
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts]
  have data := ranges row member _ port
  simpa [Trace.Proofs.read_word,importedConstraintsMemoryPorts,
    WordColumns.evaluate,dataWord] using data

/-- Original public decoding, actual word ranges and native controls derive
    the byte/halfword load result. No read/result, alignment, sign or size is
    supplied. Architectural ROM bytes and original instruction execution remain separate. -/
theorem image_native_loads {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment ∧ NativeLoadEffects trace.rom row.assignment entry := by
  have ranges := (image_value_bounds image inputs accepted decoded).1
  have addresses := image_native_addresses image inputs accepted decoded
  intro row present
  obtain ⟨entry,member,source,fields,geometry⟩ := addresses row present
  have bound := data_bound_of_reads ranges row present
  have native := accepted.constraints row present
  cases row with
  | mk family w =>
    cases family
    change DecodedFields w entry at fields
    have controls := entry_data_controls native fields
    exact ⟨entry,member,source,fields,geometry,controls.1,controls.2.1,
      controls.2.2.1,controls.2.2.2,entry_load_effect native geometry fields bound⟩

end Airbender.SubwordMemory.Proofs
