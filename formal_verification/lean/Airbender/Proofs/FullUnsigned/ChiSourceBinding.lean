import Airbender.Proofs.FullUnsigned.Source.ChiBinding
import Airbender.Proofs.FullUnsigned.ChiSourceMembership

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- The original chi5 source has canonical rows under its native query tags. -/
theorem chi_original_source_rows [Fact babyBearModulus.Prime] :
    GuardedSetupRows (include_str "../../../artifacts/setup/keccak-chi5.json")
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic")
      (fun row => row[10] = 65 ∨ row[10] = 66) := by
  change GuardedSetupRows Airbender.Setup.SourceCaptureChiLiteral.original _ _
  rw [← Airbender.Setup.SourceCaptureChiProofs.source_eq]
  exact chi_source_rows

end Airbender.Compiler.MachineTargets.Proofs
