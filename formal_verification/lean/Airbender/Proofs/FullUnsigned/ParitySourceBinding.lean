import Airbender.Proofs.FullUnsigned.Source.ParityBinding
import Airbender.Proofs.FullUnsigned.ParitySourceMembership

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- The original native source has the proved parity table rows. -/
theorem parity_original_source_rows [Fact babyBearModulus.Prime] :
    FixedSetupRows (include_str "../../../artifacts/setup/keccak-column-parity.json")
      Keccak.Split.Native.Fixed.columnParityGenericTable := by
  change FixedSetupRows Airbender.Setup.SourceCaptureParityLiteral.original _
  rw [← Airbender.Setup.SourceCaptureParityProofs.source_eq]
  exact parity_source_rows

end Airbender.Compiler.MachineTargets.Proofs
