import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.FullUnsigned.Source.ThetaLiteral
import Airbender.Proofs.FullUnsigned.Source.ThetaBytes
import Airbender.Proofs.FullUnsigned.Source.ThetaBank
import Airbender.Proofs.FullUnsigned.SourceBindingCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_string_binding Airbender.Setup.SourceCaptureThetaProofs
  using Airbender.Setup.SourceCaptureTheta
  against Airbender.Keccak.Split.Native.Fixed.thetaRhoGenericSourceBytes
  with Airbender.Setup.SourceCaptureThetaLiteral
  bytes Airbender.Setup.SourceCaptureThetaBytes
  bank Airbender.Setup.SourceCaptureThetaBank
