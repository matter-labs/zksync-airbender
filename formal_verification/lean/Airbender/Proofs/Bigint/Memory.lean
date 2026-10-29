import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Delegation.Values
import Airbender.Proofs.Bigint.Lookups
import Airbender.Proofs.Bigint.AdditiveGates
import Airbender.Proofs.Bigint.MultiplicationFields
import Airbender.Proofs.Bigint.MultiplicationWriteback

namespace Airbender.Bigint.Proofs
open Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private theorem operation_cases [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    (∀ i : Fin 7, w Variables.operations[i] = 0) ∨ ∃ i : Fin 7, w Variables.operations[i] = 1 := by
  by_cases selected : ∃ i : Fin 7, w Variables.operations[i] = 1
  · exact Or.inr selected
  · left
    intro i
    have bit : w Variables.operations[i] = 0 ∨ w Variables.operations[i] = 1 := by
      fin_cases i
      all_goals first
        | exact Control.Proofs.control_bits h 0 | exact Control.Proofs.control_bits h 1
        | exact Control.Proofs.control_bits h 2 | exact Control.Proofs.control_bits h 3
        | exact Control.Proofs.control_bits h 4 | exact Control.Proofs.control_bits h 5
        | exact Control.Proofs.control_bits h 7
    exact bit.resolve_right (fun one => selected ⟨i, one⟩)

private theorem empty_writes [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (empty : ∀ i : Fin 7, w Variables.operations[i] = 0) :
    (∀ i : Fin 16, w Variables.writtenLimbs[i] = 0) ∧ w 57 = 0 ∧ w 58 = 0 := by
  have f0 := empty 0
  have f1 := empty 1
  have f2 := empty 2
  have f3 := empty 3
  have f4 := empty 4
  have f5 := empty 5
  have f6 := empty 6
  norm_num [Variables.operations] at f0 f1 f2 f3 f4 f5 f6
  constructor
  · intro i
    have gate := Verification.assertion_of_holds h ⟨67 + i.val,
      by rw [constraint_count]; have := i.isLt; omega⟩
    fin_cases i
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, f0, f1, f2, f3, f4, f5, f6] at gate
    all_goals simpa [Variables.writtenLimbs] using gate
  · have low := Verification.assertion_of_holds h ⟨89, by rw [constraint_count]; decide⟩
    have high := Verification.assertion_of_holds h ⟨90, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, f0, f1, f2, f3, f5, f6] at low high
    exact ⟨low, high⟩

theorem written_limb_bounds [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    ∀ i : Fin 16, (w Variables.writtenLimbs[i]).val < limbBase := by
  rcases operation_cases h with empty | ⟨chosen, selected⟩
  · intro i
    rw [(empty_writes h empty).1 i]
    simp [limbBase]
  · fin_cases chosen
    · intro i
      rw [(Additive.Proofs.native_results (by omega) .add h selected i).2,
        ← (Additive.Proofs.native_results (by omega) .add h selected i).1]
      exact Additive.Proofs.result_ranges h i
    · intro i
      rw [(Additive.Proofs.native_results (by omega) .sub h selected i).2,
        ← (Additive.Proofs.native_results (by omega) .sub h selected i).1]
      exact Additive.Proofs.result_ranges h i
    · intro i
      rw [(Additive.Proofs.native_results (by omega) .reverseSub h selected i).2,
        ← (Additive.Proofs.native_results (by omega) .reverseSub h selected i).1]
      exact Additive.Proofs.result_ranges h i
    · intro i
      rw [Multiplication.Proofs.native_writes (by omega) .low h selected i]
      exact Multiplication.Proofs.product_ranges (by omega) h (Or.inl selected) ⟨i.val, by omega⟩
    · intro i
      rw [Multiplication.Proofs.native_writes (by omega) .high h selected i]
      have bound := Multiplication.Proofs.product_ranges (by omega) h (Or.inr selected)
        ⟨16 + i.val, by have := i.isLt; omega⟩
      change (w (131 + (16 + i.val))).val < limbBase at bound
      have index : 131 + (16 + i.val) = 147 + i.val := by omega
      rw [index] at bound
      exact bound
    · intro i
      rw [(Equality.Proofs.native_results (by omega) h selected i).2]
      exact (source_ranges hp h i).1
    · intro i
      rw [(Additive.Proofs.native_results (by omega) .copy h selected i).2,
        ← (Additive.Proofs.native_results (by omega) .copy h selected i).1]
      exact Additive.Proofs.result_ranges h i

theorem returned_control_bounds [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    (w 57 = 0 ∨ w 57 = 1) ∧ w 58 = 0 := by
  have carry : w 98 = 0 ∨ w 98 = 1 := by
    simpa using Additive.Proofs.carry_bits h 15
  rcases operation_cases h with empty | ⟨chosen, selected⟩
  · exact ⟨Or.inl (empty_writes h empty).2.1, (empty_writes h empty).2.2⟩
  · fin_cases chosen
    · obtain ⟨low, high⟩ := Additive.Proofs.returned_control (by omega) .add h selected
      exact ⟨low.symm ▸ carry, high⟩
    · obtain ⟨low, high⟩ := Additive.Proofs.returned_control (by omega) .sub h selected
      exact ⟨low.symm ▸ carry, high⟩
    · obtain ⟨low, high⟩ := Additive.Proofs.returned_control (by omega) .reverseSub h selected
      exact ⟨low.symm ▸ carry, high⟩
    · obtain ⟨low, high⟩ := Multiplication.Proofs.native_control (by omega) .low h selected
      refine ⟨?_, high⟩
      rw [low]
      split_ifs <;> simp
    · obtain ⟨low, high⟩ := Multiplication.Proofs.native_control (by omega) .high h selected
      exact ⟨Or.inl low, high⟩
    · obtain ⟨low, high⟩ := Equality.Proofs.native_control (by omega) h selected
      refine ⟨?_, high⟩
      rw [low, Equality.Proofs.native_zero_check h]
      rcases carry with zero | one
      all_goals first | rw [zero] | rw [one]
      all_goals split_ifs <;> simp
    · obtain ⟨low, high⟩ := Additive.Proofs.returned_control (by omega) .copy h selected
      exact ⟨low.symm ▸ carry, high⟩

private theorem native_write_word (w : Nat → ZMod p) (port : MemoryPort) :
    ((⟨.bigint, w⟩ : Delegation.Row p).writeToken port).word =
      ⟨((port.writeValue.getD port.readValue).evaluate w)[0].val,
        ((port.writeValue.getD port.readValue).evaluate w)[1].val⟩ := by
  simp [Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code]

theorem memory_write_rule [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setupTable))
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    ∀ port ∈ importedConstraintsMemoryPorts,
      ((⟨.bigint, w⟩ : Delegation.Row p).writeToken port).word.Bounded := by
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  have written := written_limb_bounds hp core
  have control := returned_control_bounds hp core
  have cb : (⟨(w 57).val, (w 58).val⟩ : Word).Bounded := by
    rcases control.1 with zero | one
    · simp [zero, control.2, Word.Bounded, limbBase]
    · simp [one, control.2, Word.Bounded, limbBase, ZMod.val_one'' (by omega : p ≠ 1)]
  intro port member
  simp [importedConstraintsMemoryPorts] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[0] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 0) (written 1)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 2) (written 3)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 4) (written 5)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 6) (written 7)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 8) (written 9)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 10) (written 11)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 12) (written 13)
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts,
      Word.Bounded, Variables.writtenLimbs] using And.intro (written 14) (written 15)
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[9] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[10] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[11] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[12] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[13] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[14] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[15] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[16] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, Trace.Proofs.read_word, WordColumns.evaluate,
      importedConstraintsMemoryPorts] using
      reads importedConstraintsMemoryPorts[17] (by simp [importedConstraintsMemoryPorts])
  · simpa [native_write_word, WordColumns.evaluate, importedConstraintsMemoryPorts] using cb

theorem memory_rules [Fact p.Prime] (hp : FieldCapacity.AtLeast p 65536) {data : Delegation.MemoryData p}
    (accepted : Delegation.MemoryAccepted data)
    (families : ∀ row ∈ data.rows, row.family = .bigint)
    (table : data.setup.bigint = setupTable) : Delegation.Proofs.WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have selected := families ⟨family, w⟩ member
    change family = .bigint at selected
    subst family
    have h := accepted.constraints ⟨.bigint, w⟩ member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints data.setup.bigint) at h
    rw [table] at h
    exact memory_write_rule hp h reads

end Airbender.Bigint.Proofs
