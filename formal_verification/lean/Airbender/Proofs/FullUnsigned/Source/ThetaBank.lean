import Airbender.Data.Setup.Source.Theta
import Airbender.Proofs.FullUnsigned.SourceBankReplacement
import Airbender.Proofs.FullUnsigned.SourceIndexLiteralCertificate

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_partition Airbender.Setup.ThetaSourceIndexPartition
  from Airbender.Setup.SourceCaptureTheta.entries_9296
  chunk_counts [64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 64, 7]

certify_source_index_literals Airbender.Setup.ThetaSourceLiteralIndices
  from Airbender.Setup.ThetaSourceIndexPartition

repack_source_array Airbender.Setup.SourceCaptureThetaBank
  in Airbender.Setup.SourceCaptureTheta at 9296
  with Airbender.Setup.ThetaSourceLiteralIndices
