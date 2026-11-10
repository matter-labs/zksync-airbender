import Airbender.Review.Compiler.SplitPhysicalRows
import Airbender.Proofs.FullUnsigned.SetupFields
import Airbender.Proofs.FullUnsigned.Source.Parity
import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.FullUnsigned.Source.Chi

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Only physical row membership remains after exact source and column decoding. -/
theorem parity_source_rows_of_physical (physical : SplitParityPhysicalRows)
    [Fact babyBearModulus.Prime] :
    FixedSetupRows Setup.SourceCaptureParity.source Keccak.Split.Native.Fixed.columnParityGenericTable :=
  fixed_setup_rows_of_decoded_columns Setup.SourceCaptureParityProofs.parsed
    Setup.SourceCaptureParityProofs.trace_len_decoded Setup.SourceCaptureParityProofs.columns_decoded physical

theorem theta_source_rows_of_physical (physical : SplitThetaPhysicalRows)
    [Fact babyBearModulus.Prime] :
    FixedSetupRows Setup.SourceCaptureTheta.source Keccak.Split.Native.Fixed.thetaRhoPhysicalGenericTable :=
  fixed_setup_rows_of_decoded_columns Setup.SourceCaptureThetaProofs.parsed
    Setup.SourceCaptureThetaProofs.trace_len_decoded Setup.SourceCaptureThetaProofs.columns_decoded physical

theorem chi_source_rows_of_physical (physical : SplitChiPhysicalRows)
    [Fact babyBearModulus.Prime] :
    FixedSetupRows Setup.SourceCaptureChi.source
      (Keccak.Split.Native.Fixed.chi5Generic.table "Airbender.SplitChi5Generic") :=
  fixed_setup_rows_of_decoded_columns Setup.SourceCaptureChiProofs.parsed
    Setup.SourceCaptureChiProofs.trace_len_decoded Setup.SourceCaptureChiProofs.columns_decoded physical

end Airbender.Compiler.MachineTargets.Proofs
