import Airbender.Proofs.Trace.Families.ReducedMachine.ShadowImage
import Airbender.Proofs.ReducedMachine.NativeWordMemoryPorts
import Airbender.Review.Helpers.Memory.ReducedMachineWordMemoryHistory

namespace Airbender.ReducedMachine.NativeWordMemoryDomainProofs
open Native NativeShadow Arithmetic Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Fresh native port bindings and scalar bounds derive the precise projection
    domain. Only ROM-region LW port1 is a shadow; SW port2 is retained RAM. -/
theorem port_domains {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    ∀ i : Fin 3, architecturalAddress (importedConstraintsMemoryPorts[i].address.code w) =
      (wordMemoryPortDomains w entry)[i] := by
  have ports := NativeWordMemoryPortProofs.addresses holds fields query
  have bounds := NativeWordMemoryNumericalProofs.address_bounds holds
  have domain : (4194304 ≤ (wordMemoryAddressWord w).toBitVec.toNat) ↔
      64 ≤ (wordMemoryAddressWord w).hi := by
    rw [Word.toBitVec_toNat bounds]
    have low := bounds.1
    dsimp [Word.value,limbBase] at *
    omega
  intro i
  rw [ports i]
  cases mode : entry.data.family
  · fin_cases i <;> simp [wordMemoryPortCells,wordMemoryPortDomains,mode,
      NativeShadowProofs.architectural_register,NativeShadowProofs.architectural_ram,domain]
  · have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
    have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have lower := (NativeWordMemoryShapeProofs.store_address holds mask).2.1
    have retained : 4194304 ≤ (wordMemoryAddressWord w).toBitVec.toNat := by
      rwa [Word.toBitVec_toNat bounds]
    fin_cases i <;> simp [wordMemoryPortCells,wordMemoryPortDomains,mode,
      NativeShadowProofs.architectural_register,NativeShadowProofs.architectural_ram,retained]

end Airbender.ReducedMachine.NativeWordMemoryDomainProofs
