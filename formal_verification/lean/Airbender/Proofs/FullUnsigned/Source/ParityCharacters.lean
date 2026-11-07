import Airbender.Proofs.FullUnsigned.Source.ParityLiteralData
import Airbender.Proofs.FullUnsigned.Source.ParityBytes
import Airbender.Proofs.FullUnsigned.Source.ParityBank
import Airbender.Proofs.FullUnsigned.SourceDirectBindingCertificate

set_option warningAsError true
set_option Elab.async false
-- Bound each renderer interval while avoiding repeated large cursor declarations.
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000

certify_direct_source_character_binding Airbender.Setup.SourceCaptureParityProofs
  using Airbender.Setup.SourceCaptureParity
  against Airbender.Setup.SourceCaptureParityLiteral.original
  with Airbender.Setup.SourceCaptureParityLiteral
  bytes Airbender.Setup.SourceCaptureParityBytes
  bank Airbender.Setup.SourceCaptureParityBank interval 16384
