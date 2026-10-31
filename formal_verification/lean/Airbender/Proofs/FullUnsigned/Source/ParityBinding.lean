import Airbender.Proofs.FullUnsigned.Source.ParityCharacters
import Airbender.Proofs.FullUnsigned.Source.ParityLiteral

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

close_source_string_binding Airbender.Setup.SourceCaptureParityProofs
  using Airbender.Setup.SourceCaptureParity
  against Airbender.Setup.SourceCaptureParityLiteral.original
  with Airbender.Setup.SourceCaptureParityLiteral
