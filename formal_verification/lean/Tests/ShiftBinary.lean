import Airbender.Review.Circuits.ShiftBinop.Binary
import Tests.ShiftRouting

namespace Tests.ShiftBinary
open Airbender Arithmetic Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def sample : Fin 12 → Fin 24
  | 0 => ⟨3, by decide⟩
  | 1 => ⟨4, by decide⟩
  | 2 => ⟨5, by decide⟩
  | 3 => ⟨9, by decide⟩
  | 4 => ⟨10, by decide⟩
  | 5 => ⟨11, by decide⟩
  | 6 => ⟨15, by decide⟩
  | 7 => ⟨16, by decide⟩
  | 8 => ⟨17, by decide⟩
  | 9 => ⟨21, by decide⟩
  | 10 => ⟨22, by decide⟩
  | _ => ⟨23, by decide⟩

def kind : Fin 12 → BinaryKind
  | 0 | 3 | 6 | 9 => .xor
  | 1 | 4 | 7 | 10 => .or
  | _ => .and

/-- All twelve register/immediate/x0 binary cases apply the new native result
    proof using already accepted complete native rows and actual public entries. -/
theorem concrete_results (i : Fin 12) :
    BinaryResult (assignment (sample i)) (kind i) (decide (6 ≤ i.val)) := by
  fin_cases i
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[3])
      (ShiftRouting.native_constraints ⟨3,by decide⟩) rfl (by decide +kernel) .xor rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[4])
      (ShiftRouting.native_constraints ⟨4,by decide⟩) rfl (by decide +kernel) .or rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[5])
      (ShiftRouting.native_constraints ⟨5,by decide⟩) rfl (by decide +kernel) .and rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[9])
      (ShiftRouting.native_constraints ⟨9,by decide⟩) rfl (by decide +kernel) .xor rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[10])
      (ShiftRouting.native_constraints ⟨10,by decide⟩) rfl (by decide +kernel) .or rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[11])
      (ShiftRouting.native_constraints ⟨11,by decide⟩) rfl (by decide +kernel) .and rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[15])
      (ShiftRouting.native_constraints ⟨15,by decide⟩) rfl (by decide +kernel) .xor rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[16])
      (ShiftRouting.native_constraints ⟨16,by decide⟩) rfl (by decide +kernel) .or rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[17])
      (ShiftRouting.native_constraints ⟨17,by decide⟩) rfl (by decide +kernel) .and rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[21])
      (ShiftRouting.native_constraints ⟨21,by decide⟩) rfl (by decide +kernel) .xor rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[22])
      (ShiftRouting.native_constraints ⟨22,by decide⟩) rfl (by decide +kernel) .or rfl
  · exact ShiftBinop.Proofs.entry_binary_result (entry := NativeSetup.entries[23])
      (ShiftRouting.native_constraints ⟨23,by decide⟩) rfl (by decide +kernel) .and rfl

/-- The public result root is applied to the actual original byte-read image. -/
theorem public_results (i : Fin 12) :
    ∃ entry ∈ NativeSetup.setup.program, entry.SourceWith NativeSetup.before decoderFields ∧
      decoderQuery (assignment (sample i)) = entry.query ∧ Routing (assignment (sample i)) entry ∧
      ∀ chosen, entry.data.family = binaryOperation chosen →
        BinaryResult (assignment (sample i)) chosen (decide (entry.data.rd = 0)) :=
  native_decoded_binary_result ShiftBinop.Proofs.native_fixture_image
    (ShiftRouting.native_constraints (sample i)) (ShiftRouting.decoder_membership (sample i))

/-- Full RV32 values must not be reduced modulo Mersenne31. Negative immediates
    retain both native limbs, while x0 discards the nonzero selected result. -/
theorem signed_immediates_and_x0 :
    (right (assignment ⟨9,by decide⟩)).value = 4294967295 ∧
    (selectedWord (assignment ⟨9,by decide⟩)).value = 2147418112 ∧
    (selectedWord (assignment ⟨10,by decide⟩)).value = 4294967295 ∧
    (selectedWord (assignment ⟨4,by decide⟩)).value = 2147549183 ∧
    (writtenWord (assignment ⟨21,by decide⟩)) = ⟨0,0⟩ ∧
    (selectedWord (assignment ⟨21,by decide⟩)).value = 2147418112 := by decide +kernel

/-- Corrupting a selected-word limb violates its actual assembly equation. -/
theorem wrong_selected_word_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 55 then 0 else assignment ⟨3,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨37,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

/-- A discarded x0 write cannot expose the nonzero selected binary value. -/
theorem nonzero_x0_write_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 60 then 32767 else assignment ⟨21,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨40,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

/-- Corrupting a reconstructed byte violates its actual native inverse-256
    equation even if the altered field value is itself a valid byte. -/
theorem wrong_byte_reconstruction_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 43 then 0 else assignment ⟨3,by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨25,by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

end Tests.ShiftBinary
