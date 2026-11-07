import Airbender.Data.Setup.Keccak.ThetaRhoGeneric
import Airbender.Proofs.FullUnsigned.SourceCharacterCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_literal_characters Airbender.Setup.SourceCaptureThetaLiteral
  from Airbender.Keccak.Split.Native.Fixed.thetaRhoGenericSourceBytes
