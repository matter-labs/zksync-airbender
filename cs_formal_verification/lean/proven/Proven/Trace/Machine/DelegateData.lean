module
public import Proven.Trace.Machine.FieldCases

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
set_option warningAsError true

/-- A fetched delegation uses the admitted full-CSR native caller metadata. -/
theorem machine_delegate_fields {config : RVMachineConfig} {kind : RV.DelegationKind} {data : RVMachineDecoderData}
    (fields : rvMachineDecoderFields config (.delegate kind) = some data) :
    config.admitsDelegation kind = true ∧
      data = ⟨config.arithmeticFamily, 0, kind.csr.toNat, 0, ⟨0, 0⟩, 128, 0⟩ := by
  have extra : rvMachineExtraFields config (.delegate kind) = some data := by
    rcases machine_fields_cases fields with extra | ⟨_, ordinary, projected, _⟩ | ⟨_, ordinary, projected, _⟩
    · exact extra
    · have rejected : UnifiedReduced.rvDecoderFields (.delegate kind) = none := rfl
      rw [rejected] at projected
      cases projected
    · have rejected : rvPooledDecoderFields (.delegate kind) = none := rfl
      rw [rejected] at projected
      cases projected
  simp only [rvMachineExtraFields] at extra
  split at extra
  · exact ⟨by assumption, (Option.some.inj extra).symm⟩
  · cases extra

end Airbender.Trace.Machine.Proofs
