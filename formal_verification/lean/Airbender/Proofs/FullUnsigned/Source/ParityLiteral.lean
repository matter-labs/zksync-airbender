import Airbender.Proofs.FullUnsigned.Source.ParityLiteralData

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_literal_character_tree Airbender.Setup.SourceCaptureParityLiteral
  from Airbender.Setup.SourceCaptureParityLiteral.original
