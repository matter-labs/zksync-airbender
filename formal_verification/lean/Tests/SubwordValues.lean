import Airbender.Review.Circuits.SubwordMemory.Values
import Tests.SubwordRouting

namespace Tests.SubwordValues
open Airbender Verification SubwordMemory Tests.SubwordRoutingFixture Tests.SubwordRouting
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Offset, native trap exclusion and high-half selection hold on all six full rows. -/
theorem all_offsets (sample : Fin 6) : OffsetValues (assignment sample) :=
  native_offset_values (native_constraints sample)

theorem rom_values_0 : ROMWordValues rom (assignment ⟨0,by decide⟩) ∧
    LoadValues (assignment ⟨0,by decide⟩)
      (dataKey (assignment ⟨0,by decide⟩) (selectedLimb (assignment ⟨0,by decide⟩) 41 42)) :=
  native_rom_load_values (native_constraints ⟨0,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem rom_values_1 : ROMWordValues rom (assignment ⟨1,by decide⟩) ∧
    LoadValues (assignment ⟨1,by decide⟩)
      (dataKey (assignment ⟨1,by decide⟩) (selectedLimb (assignment ⟨1,by decide⟩) 41 42)) :=
  native_rom_load_values (native_constraints ⟨1,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem ram_values_2 : LoadValues (assignment ⟨2,by decide⟩)
    (dataKey (assignment ⟨2,by decide⟩) (selectedLimb (assignment ⟨2,by decide⟩) 32 33)) :=
  native_ram_load_values (native_constraints ⟨2,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem ram_values_3 : LoadValues (assignment ⟨3,by decide⟩)
    (dataKey (assignment ⟨3,by decide⟩) (selectedLimb (assignment ⟨3,by decide⟩) 32 33)) :=
  native_ram_load_values (native_constraints ⟨3,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem store_values_4 : StoreValues (assignment ⟨4,by decide⟩) :=
  native_store_values (native_constraints ⟨4,by decide⟩) (by decide +kernel)

theorem store_values_5 : StoreValues (assignment ⟨5,by decide⟩) :=
  native_store_values (native_constraints ⟨5,by decide⟩) (by decide +kernel)

theorem ordinary_load_write :
    #v[assignment ⟨0,by decide⟩ 39,assignment ⟨0,by decide⟩ 40] =
      #v[assignment ⟨0,by decide⟩ 60,assignment ⟨0,by decide⟩ 61] :=
  (native_load_write_cases (native_constraints ⟨0,by decide⟩) (by decide +kernel)).1 (by decide +kernel)

/-- The original nonzero signed candidate remains observable before x0 masking. -/
theorem x0_load_write :
    assignment ⟨3,by decide⟩ 60 = 32769 ∧ assignment ⟨3,by decide⟩ 61 = 65535 ∧
    #v[assignment ⟨3,by decide⟩ 39,assignment ⟨3,by decide⟩ 40] = #v[0,0] := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  exact (native_load_write_cases (native_constraints ⟨3,by decide⟩) (by decide +kernel)).2 (by decide +kernel)

theorem store_unused_fields :
    assignment ⟨4,by decide⟩ 42 = 0 ∧ assignment ⟨4,by decide⟩ 45 = 0 :=
  store_values_4.unused

theorem changed_rom_candidate_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨0,by decide⟩ 60 0))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨32,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem changed_ram_candidate_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨2,by decide⟩ 61 65536))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨33,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem changed_masked_load_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨0,by decide⟩ 39 0))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨36,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem nonzero_x0_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨3,by decide⟩ 39 32769))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨36,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem changed_store_low_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 39 0))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨38,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem changed_store_high_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 40 35277))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨39,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem wrong_upper_offset_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨1,by decide⟩ 25 0))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have selected := (native_offset_values holds).upper
  revert selected
  decide +kernel

theorem wrong_native_offset_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 22 2))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have selected := (native_offset_values holds).offset
  revert selected
  decide +kernel

/-- A trap row remains in the table, but accepted native controls reject it. -/
theorem native_trap_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨2,by decide⟩ 11 1))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have selected := (native_offset_values holds).trapAbsent
  revert selected
  decide +kernel

end Tests.SubwordValues
