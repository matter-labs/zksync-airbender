import Airbender.Proofs.FullUnsigned.SourceLiteralTreeCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

namespace Airbender.Setup.SourceCaptureChiLiteral

def original : String := include_str "../../../../artifacts/setup/keccak-chi5.json"

end Airbender.Setup.SourceCaptureChiLiteral

prepare_literal_character_tree Airbender.Setup.SourceCaptureChiLiteral
  from Airbender.Setup.SourceCaptureChiLiteral.original
