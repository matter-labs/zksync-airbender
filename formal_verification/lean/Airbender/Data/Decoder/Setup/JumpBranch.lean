import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder jumpBranchDecoderData from "artifacts/setup/jump-branch.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def jumpBranchSetup : PackedSetup := {
  width := jumpBranchDecoderData.columns.size
  realRows := jumpBranchDecoderData
  padding := jumpBranchDecoderDataPadding
  columnsMask := jumpBranchDecoderDataColumnsMask
  tagged := jumpBranchDecoderDataTagged
  offset := jumpBranchDecoderDataOffset
  prefixTags := jumpBranchDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
