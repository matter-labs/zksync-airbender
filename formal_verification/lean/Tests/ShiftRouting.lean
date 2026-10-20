import Tests.ShiftRoutingPart0
import Tests.ShiftRoutingPart1
import Tests.ShiftRoutingPart2
import Tests.ShiftRoutingPart3
import Tests.ShiftRoutingPart4
import Tests.ShiftRoutingPart5
import Tests.ShiftRoutingQueries
import Airbender.Review.Trace.Families.ShiftBinop.NativeDecoder

namespace Tests.ShiftRouting
open Airbender Verification ShiftBinop Trace Tests.ShiftRoutingWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All twelve native ordinary forms and all x0 variants are nonempty accepted rows. -/
theorem native_constraints (sample : Fin 24) :
    FlatOperation.ConstraintsHoldFlat (environment (assignment sample))
      ShiftBinop.importedConstraints := by
  fin_cases sample
  · exact ShiftRoutingPart0.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart0.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart0.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart0.native_constraints ⟨3, by decide⟩
  · exact ShiftRoutingPart1.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart1.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart1.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart1.native_constraints ⟨3, by decide⟩
  · exact ShiftRoutingPart2.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart2.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart2.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart2.native_constraints ⟨3, by decide⟩
  · exact ShiftRoutingPart3.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart3.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart3.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart3.native_constraints ⟨3, by decide⟩
  · exact ShiftRoutingPart4.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart4.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart4.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart4.native_constraints ⟨3, by decide⟩
  · exact ShiftRoutingPart5.native_constraints ⟨0, by decide⟩
  · exact ShiftRoutingPart5.native_constraints ⟨1, by decide⟩
  · exact ShiftRoutingPart5.native_constraints ⟨2, by decide⟩
  · exact ShiftRoutingPart5.native_constraints ⟨3, by decide⟩

theorem decoder_membership (sample : Fin 24) :
    NativeSetup.setup.table.Contains #[] (decoderQuery (assignment sample)) := by
  fin_cases sample
  · exact ⟨⟨0, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨1, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨2, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨3, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨4, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨5, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨6, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨7, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨8, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨9, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨10, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨11, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨12, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨13, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨14, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨15, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨16, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨17, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨18, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨19, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨20, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨21, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨22, by decide⟩, by decide +kernel⟩
  · exact ⟨⟨23, by decide⟩, by decide +kernel⟩

/-- Nonvacuous public theorem applications use actual original public byte reads. -/
theorem public_routing (sample : Fin 24) :
    ∃ entry ∈ NativeSetup.setup.program, entry.SourceWith NativeSetup.before decoderFields ∧
      decoderQuery (assignment sample) = entry.query ∧ Routing (assignment sample) entry :=
  native_decoded_routing ShiftBinop.Proofs.native_fixture_image
    (native_constraints sample) (decoder_membership sample)

/-- SRAI's native immediate keeps its funct7 payload, but routes sign fill first. -/
theorem srai_routing :
    Routing (assignment ⟨8, by decide⟩) NativeSetup.entries[8] := by
  apply ShiftBinop.Proofs.entry_routing (native_constraints ⟨8, by decide⟩)
  · rfl
  · decide +kernel

theorem wrong_sign_fill_tag_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 46 then 50 else assignment ⟨8, by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨28, by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

theorem wrong_immediate_operand_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 27 then 0 else assignment ⟨8, by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨13, by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

theorem injected_csr_bit_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 21 then 1 else assignment ⟨3, by decide⟩ i))
      ShiftBinop.importedConstraints := by
  intro holds
  have wrong := assertion_of_holds holds ⟨47, by rw [ShiftBinop.constraint_count]; decide⟩
  revert wrong
  decide +kernel

end Tests.ShiftRouting
