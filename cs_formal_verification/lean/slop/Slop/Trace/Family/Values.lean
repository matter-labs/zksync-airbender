module
public import Slop.Trace.Family.Timestamps
public import Slop.Trace.Values
public import Slop.AddSub
public import Slop.Trace.Family.History
public import Slop.WordMemory

@[expose] public section

namespace Airbender.Trace.Proofs
open Arithmetic

/-- A write either has locally checked bounds, or copies a read no later than
    itself. This includes timestamp-refresh writes on readonly ports. -/
theorem row_write_source [Fact p.Prime] (row : Row p)
    (setup : Table (ZMod p) (fields 9))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints setup))
    (disabledROM : ∀ query, setup.Contains #[] query → query[8] = 0 → query[1] = 0 ∧ query[2] = 0)
    (rom : ∀ query, setup.Contains #[] query → query[1].val < limbBase ∧ query[2].val < limbBase)
    (port : MemoryPort) (portMember : port ∈ row.ports) :
    (writeToken row.columns row.assignment port).word.Bounded ∨
      ∃ source ∈ row.ports,
        (writeToken row.columns row.assignment port).value = (readToken row.assignment source).value ∧
        (source.event row.columns row.assignment).1 ≤ (port.event row.columns row.assignment).1 := by
  cases row with
  | mk family w =>
    cases family with
    | addSub =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
      simp [Row.ports, AddSub.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · exact Or.inr ⟨_, by simp [Row.ports, AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · exact Or.inr ⟨_, by simp [Row.ports, AddSub.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · left
        simpa [write_word, Word.Bounded] using AddSub.Proofs.written_limb_bounds core
    | wordMemory =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left (WordMemory.importedConstraints setup)
          WordMemory.importedConstraintsTimestampLookups)
      simp [Row.ports, WordMemory.importedConstraintsMemoryPorts] at portMember
      rcases portMember with rfl | rfl | rfl
      · exact Or.inr ⟨_, by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · exact Or.inr ⟨_, by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], rfl, le_rfl⟩
      · have selector : w 10 = 0 ∨ w 10 = 1 := by
          simpa using WordMemory.Proofs.local_flags core 1
        have rom : w 35 = 0 ∨ w 35 = 1 := by
          simpa using WordMemory.Proofs.local_flags core 2
        obtain ⟨store, selected⟩ : ∃ store : Bool, w 10 = if store then 1 else 0 := by
          rcases selector with hs | hs
          · exact ⟨false, hs⟩
          · exact ⟨true, hs⟩
        rcases rom with ram | inROM
        · right
          have copied := WordMemory.Proofs.ram_data disabledROM store core selected ram
          change w 31 = w 23 ∧ w 32 = w 24 at copied
          refine ⟨WordMemory.importedConstraintsMemoryPorts[1],
            by simp [Row.ports, WordMemory.importedConstraintsMemoryPorts], ?_, ?_⟩
          · simp [writeToken, readToken, MemoryPort.writeCode, MemoryPort.readCode, pairCode,
              WordMemory.importedConstraintsMemoryPorts, copied.1, copied.2]
          · change (decodeTimestamp w _).value + 1 ≤ (decodeTimestamp w _).value + 2
            omega
        · left
          have query := WordMemory.Proofs.data_lookup store core selected
          simp only [inROM, one_mul, sub_self, zero_mul, sub_zero] at query
          have ranges := rom _ query
          simpa [write_word, Word.Bounded] using ranges

end Airbender.Trace.Proofs
