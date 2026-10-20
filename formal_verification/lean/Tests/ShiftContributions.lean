import Airbender.Review.Circuits.ShiftBinop.Shifts
import Tests.ShiftRouting

namespace Tests.ShiftContributions
open Airbender Arithmetic Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def sample : Fin 12 → Fin 24
  | 0 => ⟨0,by decide⟩
  | 1 => ⟨1,by decide⟩
  | 2 => ⟨2,by decide⟩
  | 3 => ⟨6,by decide⟩
  | 4 => ⟨7,by decide⟩
  | 5 => ⟨8,by decide⟩
  | 6 => ⟨12,by decide⟩
  | 7 => ⟨13,by decide⟩
  | 8 => ⟨14,by decide⟩
  | 9 => ⟨18,by decide⟩
  | 10 => ⟨19,by decide⟩
  | _ => ⟨20,by decide⟩

def kind : Fin 12 → ShiftKind
  | 0 | 3 | 6 | 9 => .sll
  | 1 | 4 | 7 | 10 => .srl
  | _ => .sra

/-- All twelve register/immediate/x0 shift cases apply native contributions
    using complete accepted rows and original public decoder entries. -/
theorem concrete_contributions (i : Fin 12) :
    ShiftContributions (assignment (sample i)) (kind i) := by
  fin_cases i
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[0])
      (ShiftRouting.native_constraints ⟨0,by decide⟩) rfl (by decide +kernel) .sll rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[1])
      (ShiftRouting.native_constraints ⟨1,by decide⟩) rfl (by decide +kernel) .srl rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[2])
      (ShiftRouting.native_constraints ⟨2,by decide⟩) rfl (by decide +kernel) .sra rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[6])
      (ShiftRouting.native_constraints ⟨6,by decide⟩) rfl (by decide +kernel) .sll rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[7])
      (ShiftRouting.native_constraints ⟨7,by decide⟩) rfl (by decide +kernel) .srl rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[8])
      (ShiftRouting.native_constraints ⟨8,by decide⟩) rfl (by decide +kernel) .sra rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[12])
      (ShiftRouting.native_constraints ⟨12,by decide⟩) rfl (by decide +kernel) .sll rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[13])
      (ShiftRouting.native_constraints ⟨13,by decide⟩) rfl (by decide +kernel) .srl rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[14])
      (ShiftRouting.native_constraints ⟨14,by decide⟩) rfl (by decide +kernel) .sra rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[18])
      (ShiftRouting.native_constraints ⟨18,by decide⟩) rfl (by decide +kernel) .sll rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[19])
      (ShiftRouting.native_constraints ⟨19,by decide⟩) rfl (by decide +kernel) .srl rfl
  · exact ShiftBinop.Proofs.entry_shift_contributions (entry := NativeSetup.entries[20])
      (ShiftRouting.native_constraints ⟨20,by decide⟩) rfl (by decide +kernel) .sra rfl

/-- The public root is exercised against the original stateful public image. -/
theorem public_contributions (i : Fin 12) :
    ∃ entry ∈ NativeSetup.setup.program, entry.SourceWith NativeSetup.before decoderFields ∧
      decoderQuery (assignment (sample i)) = entry.query ∧ Routing (assignment (sample i)) entry ∧
      ∀ chosen, entry.data.family = chosen.operation → ShiftContributions (assignment (sample i)) chosen :=
  native_decoded_shift_contributions ShiftBinop.Proofs.native_fixture_image
    (ShiftRouting.native_constraints (sample i)) (ShiftRouting.decoder_membership (sample i))

/-- Native SRAI retains encoded funct7 in its immediate, truncates to 31 and
    adds sign fill before the two logical-shift contributions. -/
theorem srai_parts_and_shift_boundaries :
    (assignment ⟨8,by decide⟩ 27).val = 1055 ∧
    (assignment ⟨8,by decide⟩ 29).val = 31 ∧
    (partWord (assignment ⟨8,by decide⟩) 0).value = 4294967294 ∧
    (partWord (assignment ⟨8,by decide⟩) 1).value = 0 ∧
    (partWord (assignment ⟨8,by decide⟩) 2).value = 1 ∧
    (selectedWord (assignment ⟨8,by decide⟩)).value = 4294967295 ∧
    (selectedWord (assignment ⟨6,by decide⟩)).value = 2147483648 ∧
    (selectedWord (assignment ⟨7,by decide⟩)).value = 1 ∧
    (selectedWord (assignment ⟨20,by decide⟩)).value = 4294967295 ∧
    writtenWord (assignment ⟨20,by decide⟩) = ⟨0,0⟩ := by decide +kernel

/-- SLL/SRL cannot smuggle a nonzero contribution through the native inactive slot. -/
theorem nonzero_inactive_part_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 52 then 1 else assignment ⟨0,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨34,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

/-- Changing a packed source/amount key violates its actual native equation. -/
theorem wrong_packed_key_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 43 then 2064384 else assignment ⟨6,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨25,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

/-- Dropping SRA's sign-fill contribution cannot satisfy native selected assembly. -/
theorem missing_sign_fill_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 56 then 4096 else assignment ⟨2,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨38,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

end Tests.ShiftContributions
