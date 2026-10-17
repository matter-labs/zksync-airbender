import Airbender.Proofs.Trace.Families.WordMemory.Values
import Airbender.Proofs.WordMemory.Address
import Airbender.Proofs.WordMemory.PC

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Verification

/-- The first actual native port supplies the effective-address source. Its
    range follows from initialized matching, rather than a local input premise. -/
theorem image_source_bound {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) (row : Row mersenne31Modulus WordMemoryFamily)
    (member : row ∈ trace.rows) : (sourceWord row.assignment).Bounded := by
  have ranges := (image_value_bounds (by decide) inputs accepted decoded).1
  have port : importedConstraintsMemoryPorts[0] ∈ row.ports := by
    cases row with
    | mk family w =>
      cases family
      change _ ∈ importedConstraintsMemoryPorts
      simp [importedConstraintsMemoryPorts]
  have source := ranges row member _ port
  simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts,
    WordColumns.evaluate, sourceWord] using source

/-- Public indexed setup, initialized reads and native equations discharge all
    local numerical interfaces. Both address and PC arithmetic retain RV32 wrap. -/
theorem image_native_effects {trace : Data mersenne31Modulus WordMemoryFamily}
    {setup : DecoderSetup} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (inputs : ImageBoundary trace before cells)
    (image : decoderSetupImage before count logCapacity = some setup)
    (accepted : Accepted trace) (decoded : Decoded trace setup) :
    ∀ row ∈ trace.rows,
      (addressWord row.assignment).toBitVec =
        (sourceWord row.assignment).toBitVec + (immediateWord row.assignment).toBitVec ∧
      row.start.word.Bounded ∧ row.start.word.lo % 4 = 0 ∧
      row.finish.word.Bounded ∧ row.finish.word.toBitVec = row.start.word.toBitVec + 4 ∧
      ClockEffects row.columns row.assignment := by
  intro row member
  have source := image_source_bound inputs accepted decoded row member
  have words := decoded_word_bounds (by decide) image accepted decoded row member
  have aligned := decoded_pc_aligned (by decide) image accepted decoded row member
  have clock := Trace.Proofs.trace_clocks (by decide) accepted
    (Trace.Proofs.image_clock_boundary (by decide) inputs) row member
  have native := accepted.constraints row member
  cases row with
  | mk family w =>
    cases family
    have address := effective_address native source words.2
    have pc := native_pc_successor (final := Word.mk (w 13).val (w 14).val) (by decide) native
      ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ words.1 aligned
    exact ⟨address, words.1, aligned, pc.1, pc.2, clock⟩

end Airbender.WordMemory.Proofs
