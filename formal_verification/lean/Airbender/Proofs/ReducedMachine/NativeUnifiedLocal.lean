import Airbender.Proofs.ReducedMachine.NativeUnifiedDecoder
import Airbender.Proofs.ReducedMachine.NativeSupportedLocal
import Airbender.Proofs.ReducedMachine.NativeWordMemoryPreservation
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryZeroRegister
import Airbender.Proofs.ReducedMachine.NativeWordMemoryDomains
import Airbender.Review.Helpers.Memory.ReducedMachineUnified

namespace Airbender.ReducedMachine.NativeUnifiedLocalProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All seven actual profile rules feed ONE common initialized range induction.
    JAL return alignment is derived from public incoming PC before that induction. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily) {entry : UnifiedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) (aligned : row.start.word.lo%4 = 0) : RowWriteBoundsFromReads row := by
  rcases NativeUnifiedDecoderProofs.entry_profile fields with
    ⟨selected,_,_,_,selectedFields,_,same⟩ | ⟨selected,_,_,_,selectedFields,_,same⟩
  · exact NativeSupportedLocalProofs.row_write_rule row native selectedFields (query.trans same.symm) aligned
  · exact NativeWordMemoryPreservationProofs.row_write_rule row native selectedFields (query.trans same.symm)

/-- Actual masked GPR writes and actual unmasked SW memory writes preserve x0
    under the common initialized history, retaining all readonly/OLDREAD events. -/
theorem row_zero_preserving (row : Row mersenne31Modulus NativeReducedFamily) {entry : UnifiedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : RowZeroPreserving row := by
  rcases NativeUnifiedDecoderProofs.entry_profile fields with
    ⟨selected,_,_,_,selectedFields,_,same⟩ | ⟨selected,_,_,_,selectedFields,_,same⟩
  · exact NativeSupportedLocalProofs.row_zero_preserving row native selectedFields (query.trans same.symm)
  · exact NativeWordMemoryHistoryProofs.row_zero_preserving row native selectedFields (query.trans same.symm)

/-- Derive EVERY actual port domain. Supported GPR events are all retained;
    LW erases ONLY the ROM shadow from Sail, while SW memory/OLDREAD stays. -/
theorem port_domains {w : Nat → ZMod mersenne31Modulus} {entry : UnifiedProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : unifiedDecoderFields entry.instruction = some entry.data) (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, architecturalAddress (importedConstraintsMemoryPorts[i].address.code w) = (unifiedPortDomains w entry)[i] := by
  rcases NativeUnifiedDecoderProofs.entry_profile fields with
    ⟨selected,_,_,_,selectedFields,data,same⟩ | ⟨selected,_,_,_,selectedFields,data,same⟩
  · intro i
    have present : importedConstraintsMemoryPorts[i] ∈ importedConstraintsMemoryPorts := by
      fin_cases i <;> simp [importedConstraintsMemoryPorts]
    have query' : (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily).decoderQuery = selected.query := query.trans same.symm
    obtain ⟨code,address⟩ := NativeSupportedLocalProofs.row_register_space ⟨.reduced,w⟩ native selectedFields query'
      importedConstraintsMemoryPorts[i] present
    rw [address]
    simp [unifiedPortDomains,data,DecoderData.mapFamily,architecturalAddress,shadow,Nat.unpair_pair]
    fin_cases i <;> rfl
  · have actual := NativeWordMemoryDomainProofs.port_domains native selectedFields (query.trans same.symm)
    intro i
    simpa [unifiedPortDomains,data,DecoderData.mapFamily,wordMemoryPortDomains] using actual i

end Airbender.ReducedMachine.NativeUnifiedLocalProofs
