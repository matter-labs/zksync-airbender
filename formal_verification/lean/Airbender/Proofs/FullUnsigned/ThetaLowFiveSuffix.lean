import Airbender.Proofs.FullUnsigned.SetupSourceTails
import Airbender.Proofs.FullUnsigned.Source.Theta
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
certify_source_suffix Airbender.Setup.ThetaLowFiveSuffix
  from Airbender.Setup.SourceCaptureTheta.entries_9296 keep_count 316
