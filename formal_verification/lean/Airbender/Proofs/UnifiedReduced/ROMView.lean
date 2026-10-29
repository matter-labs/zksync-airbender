import Airbender.Review.Helpers.UnifiedReduced.NativeROM
import Airbender.Proofs.UnifiedReduced.ArtifactChecks
import Airbender.Proofs.UnifiedReduced.ROMLookups
import Airbender.Proofs.Trace.ROMView

namespace Airbender.UnifiedReduced.ROMView
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- A numbered original equation, keeping the imported expression opaque during composition. -/
private def assertionAt [Fact p.Prime] (setup : Table (ZMod p) (fields 10))
    (w : Nat → ZMod p) (i : Fin 120) : Prop :=
  ((FlatOperation.constraints (importedConstraints setup)).get
    ⟨i.val, by rw [constraint_count]; exact i.isLt⟩).eval (Verification.environment w) = 0

private theorem read_assertions0 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨0 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨0 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions1 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨16 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨16 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions2 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨32 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨32 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions3 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨48 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨48 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions4 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨64 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨64 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions5 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨80 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨80 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions6 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 16) :
    assertionAt setup (readData w lo hi) ⟨96 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨96 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions7 [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (_load : w 28 = 1) (_store : w 29 = 0) (_rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (_other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (_binary : w 26 = 0 ∧ w 27 = 0) (_enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 8) :
    assertionAt setup (readData w lo hi) ⟨112 + i.val, by have := i.isLt; omega⟩ := by
  have _a0 : w 11 = 0 := arithmetic 0
  have _a1 : w 12 = 0 := arithmetic 1
  have _a2 : w 13 = 0 := arithmetic 2
  have _a3 : w 14 = 0 := arithmetic 3
  have _a4 : w 15 = 0 := arithmetic 4
  have _a5 : w 16 = 0 := arithmetic 5
  have _a6 : w 17 = 0 := arithmetic 6
  have _a7 : w 18 = 0 := arithmetic 7
  have _a8 : w 19 = 0 := arithmetic 8
  have _a9 : w 20 = 0 := arithmetic 9
  have original := Verification.assertion_of_holds core
    ⟨112 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  clear core arithmetic
  fin_cases i
  all_goals simp_all [assertionAt, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, readData]

private theorem read_assertions [Fact p.Prime]
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (load : w 28 = 1) (store : w 29 = 0) (rom : w 54 = 1)
    (arithmetic : ∀ i : Fin 10, w (11 + i.val) = 0)
    (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (binary : w 26 = 0 ∧ w 27 = 0) (enabled : w 81 = 1) (lo hi : ZMod p)
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (i : Fin 120) : assertionAt setup (readData w lo hi) i := by
  by_cases h0 : i.val < 16
  · have checked := read_assertions0 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 0, by have := i.isLt; omega⟩
    have index : (⟨0 + (i.val - 0), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 0 + (i.val - 0) = i.val by omega)
    exact index ▸ checked
  by_cases h1 : i.val < 32
  · have checked := read_assertions1 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 16, by have := i.isLt; omega⟩
    have index : (⟨16 + (i.val - 16), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 16 + (i.val - 16) = i.val by omega)
    exact index ▸ checked
  by_cases h2 : i.val < 48
  · have checked := read_assertions2 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 32, by have := i.isLt; omega⟩
    have index : (⟨32 + (i.val - 32), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 32 + (i.val - 32) = i.val by omega)
    exact index ▸ checked
  by_cases h3 : i.val < 64
  · have checked := read_assertions3 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 48, by have := i.isLt; omega⟩
    have index : (⟨48 + (i.val - 48), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 48 + (i.val - 48) = i.val by omega)
    exact index ▸ checked
  by_cases h4 : i.val < 80
  · have checked := read_assertions4 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 64, by have := i.isLt; omega⟩
    have index : (⟨64 + (i.val - 64), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 64 + (i.val - 64) = i.val by omega)
    exact index ▸ checked
  by_cases h5 : i.val < 96
  · have checked := read_assertions5 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 80, by have := i.isLt; omega⟩
    have index : (⟨80 + (i.val - 80), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 80 + (i.val - 80) = i.val by omega)
    exact index ▸ checked
  by_cases h6 : i.val < 112
  · have checked := read_assertions6 load store rom arithmetic other binary enabled lo hi core
      ⟨i.val - 96, by have := i.isLt; omega⟩
    have index : (⟨96 + (i.val - 96), by have := i.isLt; omega⟩ : Fin 120) = i :=
      Fin.ext (show 96 + (i.val - 96) = i.val by omega)
    exact index ▸ checked
  have checked := read_assertions7 load store rom arithmetic other binary enabled lo hi core
    ⟨i.val - 112, by have := i.isLt; omega⟩
  have index : (⟨112 + (i.val - 112), by have := i.isLt; omega⟩ : Fin 120) = i :=
    Fin.ext (show 112 + (i.val - 112) = i.val by omega)
  exact index ▸ checked

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
  have selected := Verification.assertion_of_holds core ⟨39, by rw [constraint_count]; decide⟩
  have enabled : w 81 = 1 := by
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load, rom] at selected
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
      have checked := read_assertions load store rom arithmetic other binary enabled lo hi core
        ⟨i.val, by simpa only [constraint_count] using i.isLt⟩
      exact checked
    · intro query member
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      have original := Verification.lookup_of_holds core i
      fin_cases i
      all_goals simpa [importedConstraints, FlatOperation.lookups, Lookup.Contains, Verification.range16, Table.toRaw, Expression.eval,
        Verification.environment, readData, load, store, rom, enabled,
        a0, a1, a2, a3, a4, a5, a6, a7, a8, a9,
        other.1, other.2.1, other.2.2.1, other.2.2.2, binary.1, binary.2] using original
  · have timestamps := Verification.holds_of_sublist holds
      (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
    simpa [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat, Expression.eval,
      Verification.environment, readData, Trace.timestampLookup, Lookup.Contains, Verification.range16, Table.toRaw] using timestamps

end Airbender.UnifiedReduced.ROMView
