import Airbender.Proofs.FullUnsigned.SetupSourceTails
import Airbender.Proofs.FullUnsigned.Source.Chi

set_option warningAsError true
set_option Elab.async false
-- Each literal source list has at most 1,024 entries. Long lists use the proved decoder.
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column0
  from Airbender.Setup.SourceCaptureChi.entries_2452 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column1
  from Airbender.Setup.SourceCaptureChi.entries_2458 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column2
  from Airbender.Setup.SourceCaptureChi.entries_2579 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column3
  from Airbender.Setup.SourceCaptureChi.entries_2619 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column4
  from Airbender.Setup.SourceCaptureChi.entries_2645 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column5
  from Airbender.Setup.SourceCaptureChi.entries_2715 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column6
  from Airbender.Setup.SourceCaptureChi.entries_2804 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column7
  from Airbender.Setup.SourceCaptureChi.entries_2871 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column8
  from Airbender.Setup.SourceCaptureChi.entries_3333 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column9
  from Airbender.Setup.SourceCaptureChi.entries_3369 keep_count 122

certify_source_suffix Airbender.Setup.ChiControllerSuffix.Column10
  from Airbender.Setup.SourceCaptureChi.entries_3373 keep_count 122
