import Human.Helpers.UnifiedReduced.NativeROM
import Slop.UnifiedReduced.ArtifactChecks
import Slop.UnifiedReduced.ROMLookups
import Slop.UnifiedReduced.OpIndex
import Slop.Trace.ROMView

namespace Airbender.UnifiedReduced.ROMView
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem read_data_unused [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (load : w 28 = 1) (store : w 29 = 0) (rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (lo hi : ZMod p)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (clockConstraints setup)) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (readData w lo hi)) (clockConstraints setup) := by
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have selected := Verification.assertion_of_holds core ⟨42, by rw [constraint_count]; decide⟩
  have enabled : w 87 = 1 := by
    op_index at selected
    simp only [Expression.eval, Verification.environment, load, rom] at selected
    push_cast at selected
    linear_combination selected
  have a0 : w 11 = 0 := arithmetic 0
  have a1 : w 12 = 0 := arithmetic 1
  have a2 : w 13 = 0 := arithmetic 2
  have a3 : w 14 = 0 := arithmetic 3
  have a4 : w 15 = 0 := arithmetic 4
  have a5 : w 16 = 0 := arithmetic 5
  have a6 : w 17 = 0 := arithmetic 6
  have a7 : w 18 = 0 := arithmetic 7
  have a8 : w 19 = 0 := arithmetic 8
  have a9 : w 20 = 0 := arithmetic 9
  apply Verification.holds_append
  · apply FlatOperation.constraintsHoldFlat_iff_forall_mem.mpr
    constructor
    · intro expression member
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      have original := Verification.assertion_of_holds core i
      obtain ⟨k, hk⟩ := i
      have bound : k < 129 := by have := hk; rwa [constraint_count] at this
      interval_cases k
      all_goals first
        | (op_index at original ⊢
           simp only [Expression.eval, Verification.environment, readData, load, store, rom, enabled,
            a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] at original ⊢
           push_cast at original ⊢
           exact original)
        | (simp [importedConstraints, FlatOperation.constraints, Expression.eval,
            Verification.environment, readData, load, store, rom, enabled,
            a0, a1, a2, a3, a4, a5, a6, a7, a9,
            other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] at original ⊢ <;> exact original)
    · intro query member
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      have original := Verification.lookup_of_holds core i
      obtain ⟨k, hk⟩ := i
      have bound : k < 18 := by have := hk; rwa [lookup_count] at this
      interval_cases k
      all_goals first
        | (op_index at original ⊢
           simpa only [Lookup.Contains, Verification.range16, Table.toRaw, Expression.eval,
            Verification.environment, readData, load, store, rom, enabled,
            a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] using original)
        | (simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, Verification.range16, Table.toRaw, Expression.eval,
            Verification.environment, readData, load, store, rom, enabled,
            a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
            other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] using original)
  · have timestamps := Verification.holds_of_sublist holds
      (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
    simpa [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat, Expression.eval,
      Verification.environment, readData, Trace.timestampLookup, Lookup.Contains, Verification.range16, Table.toRaw] using timestamps

end Airbender.UnifiedReduced.ROMView
