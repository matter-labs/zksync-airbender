import Airbender.Proofs.FullUnsigned.Source.ChiCharacters
import Airbender.Proofs.FullUnsigned.Source.ChiLiteral

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

close_source_string_binding Airbender.Setup.SourceCaptureChiProofs
  using Airbender.Setup.SourceCaptureChi
  against Airbender.Setup.SourceCaptureChiLiteral.original
  with Airbender.Setup.SourceCaptureChiLiteral
