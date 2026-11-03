import Airbender.Data.Setup.Keccak.ThetaRhoGeneric
import Airbender.Proofs.FullUnsigned.SourceLiteralTreeCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

prepare_literal_character_tree Airbender.Setup.SourceCaptureThetaLiteral
  from Airbender.Keccak.Split.Native.Fixed.thetaRhoGenericSourceBytes

certify_literal_character_tree Airbender.Setup.SourceCaptureThetaLiteral
  from Airbender.Keccak.Split.Native.Fixed.thetaRhoGenericSourceBytes
