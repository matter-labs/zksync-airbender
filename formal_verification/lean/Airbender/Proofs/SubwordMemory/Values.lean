import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Proofs.SubwordMemory.Stores
import Airbender.Proofs.SubwordMemory.ROM
import Airbender.Proofs.Trace.Values

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace

/-- Imported table/merge equations preserve bounds from the source and old
    cell reads. Readonly ports preserve their own words. No result is assumed. -/
theorem write_rules {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    {trace : NativeTrace p} (accepted : Accepted trace) {program : Nat → BitVec 32}
    (setup : trace.rom = Verification.subwordTable program) :
    Trace.Proofs.WriteBoundsFromReads trace := by
  intro row member port present reads
  have core := Verification.holds_of_sublist (accepted.constraints row member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  rw [setup] at core
  simp [Row.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl
  · exact reads _ (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl
  · have active := accepted.active row member
    have choose (column : Nat) (flag : row.assignment column = 0 ∨ row.assignment column = 1) :
        ∃ value : Bool, row.assignment column = if value then 1 else 0 := by
      rcases flag with flag | flag
      · exact ⟨false, flag⟩
      · exact ⟨true, flag⟩
    obtain ⟨store, selected⟩ := choose 10 (local_flags core 1)
    obtain ⟨byte, byteSelection⟩ := choose 11 (local_flags core 2)
    obtain ⟨highByte, bit0⟩ := choose 35 (local_flags core 4)
    obtain ⟨highHalf, bit1⟩ := choose 36 (local_flags core 5)
    have output : (Word.mk (row.assignment 33).val (row.assignment 34).val).Bounded := by
      cases store
      · change row.assignment 10 = 0 at selected
        rcases local_flags core 8 with ram | rom
        · exact ram_output_bounds (by omega) byte core active selected ram byteSelection
        · have query := rom_load_query core active selected rom
          apply Verification.subword_rom_bounds hp byte query
          cases byte <;> simp [byteSelection]
      · change row.assignment 10 = 1 at selected
        have forbid := Verification.assertion_of_holds core ⟨11, by rw [constraint_count]; decide⟩
        have ram : row.assignment 41 = 0 := by
          simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
            Verification.environment, selected] using forbid
        have source : (Word.mk (row.assignment 25).val (row.assignment 26).val).Bounded := by
          have bounded := reads importedConstraintsMemoryPorts[1]
            (by simp [Row.ports, importedConstraintsMemoryPorts]) (by
              change (decodeTimestamp row.assignment _).value + 1 ≤ (decodeTimestamp row.assignment _).value + 2
              omega)
          simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using bounded
        have old : (Word.mk (row.assignment 31).val (row.assignment 32).val).Bounded := by
          simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using
            reads importedConstraintsMemoryPorts[2] (by simp [Row.ports, importedConstraintsMemoryPorts]) le_rfl
        have merged := store_data (by omega) byte highByte highHalf core active selected ram byteSelection
          bit0 bit1 ⟨(ZMod.natCast_zmod_val _).symm,
            (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩ source old
        rw [merged.2]
        exact merged.1
    simpa [Trace.Proofs.write_word, importedConstraintsMemoryPorts] using output

/-- Public seed bounds propagate through native matching to every operand,
    merged write and terminal token using the shared time induction. -/
theorem native_value_bounds {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    (seed : ∀ token ∈ trace.initialMemory, token.word.Bounded) {program : Nat → BitVec 32}
    (setup : trace.rom = Verification.subwordTable program) :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
      (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
        (writeToken row.columns row.assignment port).word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have rules := write_rules hp accepted setup
  exact ⟨Trace.Proofs.read_bounds_of_rules clockSize inverse accepted clocks seed rules,
    Trace.Proofs.write_bounds_of_rules clockSize inverse accepted clocks seed rules,
    Trace.Proofs.terminal_bounds_of_rules clockSize inverse accepted clocks seed rules⟩

end Airbender.SubwordMemory.Proofs
