import Airbender.Proofs.Trace.Families.SubwordMemory.Values
import Airbender.Proofs.SubwordMemory.Address

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Verification
set_option autoImplicit false

/-- The actual first native port supplies the source range through initialized
    value history, retaining readonly refreshes and register aliases. -/
theorem source_bound_of_reads {trace : Data mersenne31Modulus SubwordMemoryFamily}
    (ranges : ∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (readToken row.assignment port).word.Bounded)
    (row : Row mersenne31Modulus SubwordMemoryFamily) (member : row ∈ trace.rows) :
    (sourceWord row.assignment).Bounded := by
  have port : importedConstraintsMemoryPorts[0] ∈ row.ports := by
    cases row with
    | mk family w =>
      cases family
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts]
  have source := ranges row member _ port
  simpa [Trace.Proofs.read_word,importedConstraintsMemoryPorts,
    WordColumns.evaluate,sourceWord] using source

/-- Actual original public decoding derives immediate/raw/x0 interfaces; native
    equations and initialized source bounds derive the byte and port addresses. -/
theorem image_native_addresses {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows, ∃ entry ∈ setup.program,
      entry.SourceWith before decoderFields ∧ DecodedFields row.assignment entry ∧
      NativeAddress row.assignment := by
  have ranges := (image_value_bounds image inputs accepted decoded).1
  intro row present
  have bound := source_bound_of_reads ranges row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,entryMember,source,fields⟩ := fetched_fields image native member
    change DecodedFields w entry at fields
    have immediate : (immediateWord w).Bounded := by
      change (⟨(w 9).val,(w 10).val⟩ : Word).Bounded
      rw [fields.immediate]
      exact (decoder_field_bounds source.fields).1
    have funct : (w 11).val < 8 := by
      rw [fields.funct3]
      cases entry.data.family <;> decide +kernel
    have zero : w 8 = 0 ∨ w 8 = 1 := by
      rw [fields.zero]
      split_ifs <;> simp
    exact ⟨entry,entryMember,source,fields,native_address native bound immediate funct zero⟩

end Airbender.SubwordMemory.Proofs
