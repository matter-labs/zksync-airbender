import Airbender.Proofs.FullUnsigned.SourceLiteralTreeCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

namespace Airbender.Setup.SourceCaptureParityLiteral

def original : String := include_str "../../../../artifacts/setup/keccak-column-parity.json"

end Airbender.Setup.SourceCaptureParityLiteral

prepare_literal_character_tree Airbender.Setup.SourceCaptureParityLiteral
  from Airbender.Setup.SourceCaptureParityLiteral.original
