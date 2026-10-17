import Airbender.Proofs.Trace.Families.WordMemory.History
import Airbender.Proofs.Trace.Families.WordMemory.Decoder
import Airbender.Proofs.Trace.Values
import Airbender.Proofs.WordMemory.Transfers

namespace Airbender.WordMemory.Proofs
open Arithmetic Trace Verification
open Airbender.Trace.Proofs

/-- All words stored by the last native port remain bounded. Stores copy the
    earlier operand port; loads select either bounded ROM data or the RAM read.
    The decoder, rather than a local premise, supplies the zero flag below. -/
theorem written_limb_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} {w : Nat → ZMod p}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (flag : w 8 = 0 ∨ w 8 = 1)
    (read : (Word.mk (w 30).val (w 31).val).Bounded) :
    (Word.mk (w 37).val (w 38).val).Bounded := by
  have effects := transfers hp native
  rcases effects.storeBit with load | store
  · have values := effects.load load
    by_cases region : (w 20).val < 64
    · simp only [region, if_true] at values
      rcases flag with zero | one
      · simp only [zero, sub_zero, one_mul] at values
        rw [values.1, values.2]
        have bounds := Word.ofBitVec_bound
          (rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4))
        change _ % 65536 < 65536 ∧ _ / 65536 < 65536 at bounds
        have lower : (rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4)).toNat % 65536 < p :=
          lt_trans bounds.1 (by omega)
        have upper : (rom.word (((w 19).val + 65536 * ((w 20).val % 64)) / 4)).toNat / 65536 < p :=
          lt_trans bounds.2 (by omega)
        simpa only [Word.Bounded, limbBase, ZMod.val_natCast,
          Nat.mod_eq_of_lt lower, Nat.mod_eq_of_lt upper] using bounds
      · simp only [one, sub_self, zero_mul] at values
        simp [values.1, values.2, Word.Bounded, limbBase]
    · simp only [region, if_false] at values
      rcases flag with zero | one
      · simp only [zero, sub_zero, one_mul] at values
        simpa only [values.1, values.2] using read
      · simp only [one, sub_self, zero_mul] at values
        simp [values.1, values.2, Word.Bounded, limbBase]
  · have values := effects.store store
    simpa only [values.2.1, values.2.2] using read

/-- The only data dependency of the final write is the earlier native port.
    Readonly refreshes preserve their own read, including ROM-shadow accesses. -/
theorem row_write_rule {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {rom : WordROM} (row : Row p WordMemoryFamily)
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (row.constraints rom))
    (flag : row.assignment row.decoderColumns.rdIsZero = 0 ∨
      row.assignment row.decoderColumns.rdIsZero = 1) : RowWriteBoundsFromReads row := by
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
      rw [write_word]
      change (Word.mk (w 37).val (w 38).val).Bounded
      apply written_limb_bounds hp native flag
      simpa [read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using source

theorem decoded_write_rules {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    (accepted : Accepted trace) (decoded : Decoded trace setup) : WriteBoundsFromReads trace := by
  intro row member
  exact row_write_rule hp row (accepted.constraints row member)
    (decoded_zero_flag (by omega) accepted decoded row member)

theorem image_value_bounds {p : Nat} [Fact p.Prime] (hp : 4194304 < p)
    {trace : Data p WordMemoryFamily} {setup : DecoderSetup}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : Decoded trace setup) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have clocks := image_clock_boundary (by omega) inputs
  have seeds := image_bounds inputs.image
  have rules := decoded_write_rules hp accepted decoded
  exact ⟨read_bounds_of_rules clockSize accepted clocks seeds rules,
    write_bounds_of_rules clockSize accepted clocks seeds rules,
    terminal_bounds_of_rules clockSize accepted clocks seeds rules⟩

end Airbender.WordMemory.Proofs
