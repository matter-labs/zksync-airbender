import Airbender.Proofs.FullUnsigned.Source.ChiLiteralData
import Airbender.Proofs.FullUnsigned.Source.ChiBytes
import Airbender.Proofs.FullUnsigned.Source.ChiBank
import Airbender.Proofs.FullUnsigned.SourceBindingCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_character_binding Airbender.Setup.SourceCaptureChiProofs
  using Airbender.Setup.SourceCaptureChi
  against Airbender.Setup.SourceCaptureChiLiteral.original
  with Airbender.Setup.SourceCaptureChiLiteral
  bytes Airbender.Setup.SourceCaptureChiBytes
  bank Airbender.Setup.SourceCaptureChiBank interval 8192
