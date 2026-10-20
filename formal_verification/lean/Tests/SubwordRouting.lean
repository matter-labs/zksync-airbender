import Tests.SubwordRoutingPart0
import Tests.SubwordRoutingPart1
import Tests.SubwordRoutingPart2

namespace Tests.SubwordRouting
open Airbender Verification SubwordMemory Tests.SubwordRoutingFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All six samples satisfy every original native equation and lookup. -/
theorem native_constraints (sample : Fin 6) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      (SubwordMemory.importedConstraints rom) := by
  fin_cases sample
  · exact SubwordRoutingPart0.accepted_0
  · exact SubwordRoutingPart0.accepted_1
  · exact SubwordRoutingPart1.accepted_2
  · exact SubwordRoutingPart1.accepted_3
  · exact SubwordRoutingPart2.accepted_4
  · exact SubwordRoutingPart2.accepted_5

theorem all_modes (sample : Fin 6) : ModeRouting (assignment sample) :=
  native_operation_modes (native_constraints sample)

theorem rom_signed_lower : ROMLoadRouting rom (assignment ⟨0,by decide⟩) :=
  native_rom_load_routing (native_constraints ⟨0,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem rom_unsigned_upper : ROMLoadRouting rom (assignment ⟨1,by decide⟩) :=
  native_rom_load_routing (native_constraints ⟨1,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem ram_signed_odd : RAMLoadRouting (assignment ⟨2,by decide⟩) :=
  native_ram_load_routing (native_constraints ⟨2,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem ram_signed_upper_x0 : RAMLoadRouting (assignment ⟨3,by decide⟩) :=
  native_ram_load_routing (native_constraints ⟨3,by decide⟩) (by decide +kernel) (by decide +kernel)

theorem store_odd_byte : StoreRouting (assignment ⟨4,by decide⟩) :=
  native_store_routing (native_constraints ⟨4,by decide⟩) (by decide +kernel)

theorem store_halfword : StoreRouting (assignment ⟨5,by decide⟩) :=
  native_store_routing (native_constraints ⟨5,by decide⟩) (by decide +kernel)

/-- Nonzero ROM key distinguishes native word indexing from byte addressing. -/
theorem rom_word_index : assignment ⟨1,by decide⟩ 52 = 1 ∧
    assignment ⟨1,by decide⟩ 56 = 1477035 := by decide +kernel

/-- Actual stores retain the unselected limb and place the selected bytes. These
    concrete writes check the full fixtures; a general execution theorem is later. -/
theorem actual_odd_store : assignment ⟨4,by decide⟩ 39 = 17767 ∧
    assignment ⟨4,by decide⟩ 40 = 43981 := by decide +kernel

theorem actual_half_store : assignment ⟨5,by decide⟩ 39 = 4779 ∧
    assignment ⟨5,by decide⟩ 40 = 35277 := by decide +kernel

def mutated (sample : Fin 6) (column : Nat) (value : ZMod mersenne31Modulus)
    (index : Nat) : ZMod mersenne31Modulus :=
  if index = column then value else assignment sample index

theorem crossed_store_tag_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 55 55))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨14,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem wrong_rom_byte_key_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨1,by decide⟩ 52 4))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨26,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem wrong_ram_limb_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨2,by decide⟩ 46 1))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨20,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem wrong_store_old_limb_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 47 17767))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨21,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem nonzero_disabled_slot_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨2,by decide⟩ 58 1))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨31,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem rom_store_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨0,by decide⟩ 12 1))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨12,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem nonboolean_upper_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 25 2))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨2,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

theorem wrong_mixed_address_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (mutated ⟨4,by decide⟩ 35 4))
      (SubwordMemory.importedConstraints rom) := by
  intro holds
  have rejected := assertion_of_holds holds ⟨17,by rw [SubwordMemory.Proofs.constraint_count]; decide⟩
  revert rejected
  decide +kernel

end Tests.SubwordRouting
