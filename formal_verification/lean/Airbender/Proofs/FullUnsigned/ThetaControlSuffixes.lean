import Airbender.Proofs.FullUnsigned.SetupSourceTails
import Airbender.Proofs.FullUnsigned.Source.Theta

set_option warningAsError true
set_option Elab.async false
-- These source suffixes retain at most 243 blocks per column.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column0
  from Airbender.Setup.SourceCaptureTheta.entries_7040 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column1
  from Airbender.Setup.SourceCaptureTheta.entries_7064 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column2
  from Airbender.Setup.SourceCaptureTheta.entries_8478 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column3
  from Airbender.Setup.SourceCaptureTheta.entries_9296 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column4
  from Airbender.Setup.SourceCaptureTheta.entries_10186 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column5
  from Airbender.Setup.SourceCaptureTheta.entries_10204 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column6
  from Airbender.Setup.SourceCaptureTheta.entries_10212 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column7
  from Airbender.Setup.SourceCaptureTheta.entries_10220 keep_count 243

certify_source_suffix Airbender.Setup.ThetaControlSuffix.Column8
  from Airbender.Setup.SourceCaptureTheta.entries_10225 keep_count 243

