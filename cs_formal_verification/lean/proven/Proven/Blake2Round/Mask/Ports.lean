module
public import Human.Circuits.Blake2Round.Mask
public import Proven.Defs.Circuits.Blake2Round.Row

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace

/-- The imported ports agree with the existing observable word columns. -/
theorem state_reads (w : Nat → ZMod babyBearModulus) (i : Fin 8) :
    readWord w ⟨1 + i.val, by have := i.isLt; omega⟩ = (Preparation.words w Variables.stateReads)[i] := by
  fin_cases i <;> simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair, Preparation.words, Variables.stateReads]

/-- The imported ports agree with the existing observable word columns. -/
theorem extended_reads (w : Nat → ZMod babyBearModulus) (i : Fin 16) :
    readWord w ⟨9 + i.val, by have := i.isLt; omega⟩ = (Preparation.words w Variables.extendedReads)[i] := by
  fin_cases i <;> simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair, Preparation.words, Variables.extendedReads]

/-- The imported ports agree with the existing observable word columns. -/
theorem message_reads (w : Nat → ZMod babyBearModulus) (i : Fin 16) :
    readWord w ⟨26 + i.val, by have := i.isLt; omega⟩ = (Preparation.words w Variables.messageReads)[i] := by
  fin_cases i <;> simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair, Preparation.words, Variables.messageReads]

/-- The imported ports agree with the existing observable word columns. -/
theorem state_writes (w : Nat → ZMod babyBearModulus) (i : Fin 8) :
    writtenWord w ⟨1 + i.val, by have := i.isLt; omega⟩ = (Preparation.words w Finalization.stateWrites)[i] := by
  fin_cases i <;> simp [writtenWord, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair, Preparation.words, Finalization.stateWrites]

/-- The imported ports agree with the existing observable word columns. -/
theorem extended_writes (w : Nat → ZMod babyBearModulus) (i : Fin 16) :
    writtenWord w ⟨9 + i.val, by have := i.isLt; omega⟩ = (Preparation.words w Mixing.extendedWrites)[i] := by
  fin_cases i <;> simp [writtenWord, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair, Preparation.words, Mixing.extendedWrites]

/-- The native register port exposes its actual low and high value columns. -/
theorem control_read (w : Nat → ZMod babyBearModulus) :
    readWord w 42 = ⟨(w 135).val, (w 136).val⟩ := by
  simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair]

/-- The native register port exposes its actual low and high value columns. -/
theorem control_write (w : Nat → ZMod babyBearModulus) :
    writtenWord w 42 = ⟨(w 137).val, (w 138).val⟩ := by
  simp [writtenWord, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair]

/-- The native register port exposes its actual low and high value columns. -/
theorem state_pointer (w : Nat → ZMod babyBearModulus) :
    readWord w 0 = ⟨(w 3).val, (w 4).val⟩ := by
  simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair]

/-- The native register port exposes its actual low and high value columns. -/
theorem message_pointer (w : Nat → ZMod babyBearModulus) :
    readWord w 25 = ⟨(w 101).val, (w 102).val⟩ := by
  simp [readWord, readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code, WordColumns.evaluate, Nat.unpair_pair]

end Airbender.Blake2Round.Mask.Proofs
