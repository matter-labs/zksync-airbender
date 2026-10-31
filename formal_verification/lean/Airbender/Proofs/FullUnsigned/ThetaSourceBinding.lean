import Airbender.Proofs.FullUnsigned.Source.ThetaBinding
import Airbender.Proofs.FullUnsigned.ThetaSourceMembership

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- The original native source has the proved theta table rows. -/
theorem theta_original_source_rows [Fact babyBearModulus.Prime] :
    FixedSetupRows (include_str "../../../artifacts/setup/keccak-theta-rho.json")
      Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable := by
  change FixedSetupRows Keccak.Split.Native.Fixed.thetaRhoGenericSourceBytes _
  rw [← Airbender.Setup.SourceCaptureThetaProofs.source_eq]
  exact theta_source_rows

end Airbender.Compiler.MachineTargets.Proofs
