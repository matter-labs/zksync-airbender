import Airbender.Review.Helpers.Decoder.SubwordMemory
import Airbender.Proofs.Trace.Families.SubwordMemory.History
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.SubwordMemory.Decoder
import Airbender.Proofs.SubwordMemory.StoreBounds

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Verification Airbender.Trace.Proofs
set_option autoImplicit false

theorem row_decoder_query (row : Row mersenne31Modulus SubwordMemoryFamily) :
    row.decoderQuery = decoderQuery row.assignment := by
  cases row with
  | mk family w => cases family; rfl

/-- The actual decoder supplies raw funct3 and x0 masking. Loads use certified
    native candidates; stores preserve bounded source/old reads through disjoint
    native clearing and placement. No packed-key or desired-result premise. -/
theorem entry_written_bounds {rom : WordROM} {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (original : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (source : (⟨(w 32).val,(w 33).val⟩ : Word).Bounded)
    (old : (⟨(w 37).val,(w 38).val⟩ : Word).Bounded) :
    (⟨(w 39).val,(w 40).val⟩ : Word).Bounded := by
  have fields := entry_fields original query
  rcases store_bit native with load | store
  · exact (decoded_load_writes native fields load).bounded
  · have funct : (w 11).val < 8 := by
      rw [fields.funct3]
      cases entry.data.family <;> decide +kernel
    exact store_written_bounds native store funct source old

/-- Readonly ports retain their words and refresh their clocks. The actual last
    write depends on both earlier source and old-destination/RAM reads. -/
theorem row_write_rule {rom : WordROM} (row : Row mersenne31Modulus SubwordMemoryFamily)
    {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    (fields : decoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowWriteBoundsFromReads row := by
  cases row with
  | mk family w =>
    cases family
    intro port member reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · have source := reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (by
          change (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 1 ≤
            (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 2
          omega)
      have old := reads importedConstraintsMemoryPorts[2]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
      rw [write_word]
      change (⟨(w 39).val,(w 40).val⟩ : Word).Bounded
      exact entry_written_bounds native fields query
        (by simpa [read_word,importedConstraintsMemoryPorts,WordColumns.evaluate] using source)
        (by simpa [read_word,importedConstraintsMemoryPorts,WordColumns.evaluate] using old)

theorem decoded_write_rules {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) : WriteBoundsFromReads trace := by
  intro row present
  have native := accepted.constraints row present
  have member := decoded row present
  rw [row_decoder_query] at member
  cases row with
  | mk family w =>
    cases family
    obtain ⟨entry,_,source,query⟩ := fetched_sources image native member
    exact row_write_rule _ native source.fields query

theorem image_value_bounds {trace : Data mersenne31Modulus SubwordMemoryFamily}
    {setup : SparseDecoderSetup Operation} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : sparseDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have clocks := image_clock_boundary (by decide) inputs
  have seeds := image_bounds inputs.image
  have rules := decoded_write_rules image accepted decoded
  exact ⟨read_bounds_of_rules (by decide) accepted clocks seeds rules,
    write_bounds_of_rules (by decide) accepted clocks seeds rules,
    terminal_bounds_of_rules (by decide) accepted clocks seeds rules⟩

end Airbender.SubwordMemory.Proofs
