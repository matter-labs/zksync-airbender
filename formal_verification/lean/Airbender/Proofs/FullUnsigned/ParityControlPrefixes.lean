import Airbender.Proofs.FullUnsigned.SetupSourcePrefixes
import Airbender.Proofs.FullUnsigned.Source.Parity
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_prefix Airbender.Setup.ParityControlPrefix.Column0
  from Airbender.Setup.SourceCaptureParity.entries_2904 prefix_count 52
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column1
  from Airbender.Setup.SourceCaptureParity.entries_2932 prefix_count 16
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column2
  from Airbender.Setup.SourceCaptureParity.entries_3100 prefix_count 161
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column3
  from Airbender.Setup.SourceCaptureParity.entries_3177 prefix_count 58
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column4
  from Airbender.Setup.SourceCaptureParity.entries_3206 prefix_count 12
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column5
  from Airbender.Setup.SourceCaptureParity.entries_3282 prefix_count 10
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column6
  from Airbender.Setup.SourceCaptureParity.entries_3289 prefix_count 27
certify_source_prefix Airbender.Setup.ParityControlPrefix.Column7
  from Airbender.Setup.SourceCaptureParity.entries_3295 prefix_count 3
