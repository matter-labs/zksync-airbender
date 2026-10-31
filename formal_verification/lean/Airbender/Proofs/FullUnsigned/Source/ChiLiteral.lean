import Airbender.Proofs.FullUnsigned.Source.ChiLiteralData

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_literal_character_tree Airbender.Setup.SourceCaptureChiLiteral
  from Airbender.Setup.SourceCaptureChiLiteral.original
