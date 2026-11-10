import Airbender.Data.Setup.Source.Chi
import Airbender.Proofs.FullUnsigned.SourceBytesCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_byte_encodings Airbender.Setup.SourceCaptureChiBytes
  using Airbender.Setup.SourceCaptureChi
