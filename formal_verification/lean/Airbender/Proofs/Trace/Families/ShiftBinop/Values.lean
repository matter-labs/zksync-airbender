import Airbender.Review.Helpers.Decoder.ShiftBinop
import Airbender.Proofs.Trace.Families.ShiftBinop.History
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.ShiftBinop.BinaryResults
import Airbender.Proofs.ShiftBinop.ShiftSourceBounds

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Trace Verification
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem row_decoder_query (row : Row mersenne31Modulus ShiftBinopFamily) :
    row.decoderQuery = decoderQuery row.assignment := by
  cases row with
  | mk family w => cases family; rfl

/-- The six ordinary operation constructors select native binary bounds or the
    proved disjoint shift halves. No desired result is supplied. -/
theorem entry_selected_bounds {w : Nat → ZMod mersenne31Modulus} {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (source : (left w).Bounded) :
    (selectedWord w).Bounded := by
  cases family : entry.data.family
  · exact shift_selected_bounds (entry_shift_contributions native fields query .sll family) source
  · exact shift_selected_bounds (entry_shift_contributions native fields query .srl family) source
  · exact shift_selected_bounds (entry_shift_contributions native fields query .sra family) source
  · exact (entry_binary_result native fields query .xor family).selectedBound
  · exact (entry_binary_result native fields query .or family).selectedBound
  · exact (entry_binary_result native fields query .and family).selectedBound

/-- Readonly ports refresh their exact reads. The third actual write is bounded
    by the earlier source read and exact decoded x0 masking. -/
theorem row_write_rule (row : Row mersenne31Modulus ShiftBinopFamily) {entry : ProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints ()))
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
    · have first := reads importedConstraintsMemoryPorts[0]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (by
          change (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 0 ≤
            (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value + 2
          omega)
      rw [read_word] at first
      change (left w).Bounded at first
      have selected := entry_selected_bounds native fields query first
      have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) query
      change w 8 = (if entry.data.rd = 0 then 1 else 0) at flag
      have masked := written_mask native (decide (entry.data.rd = 0))
        (by simpa only [decide_eq_true_eq] using flag)
      rw [write_word]
      change (writtenWord w).Bounded
      rw [masked]
      split
      · exact ⟨by decide,by decide⟩
      · exact selected

theorem decoded_write_rules {trace : Data mersenne31Modulus ShiftBinopFamily}
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

/-- One shared history induction supplies every native read/write/terminal word
    bound from actual public seeds and checked local preservation laws. -/
theorem image_value_bounds {trace : Data mersenne31Modulus ShiftBinopFamily}
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

end Airbender.ShiftBinop.Proofs
