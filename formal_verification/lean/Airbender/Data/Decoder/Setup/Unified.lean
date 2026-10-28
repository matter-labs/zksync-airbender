import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder unifiedDecoderData from "artifacts/setup/unified.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def unifiedSetup : PackedSetup := {
  width := unifiedDecoderData.columns.size
  realRows := unifiedDecoderData
  padding := unifiedDecoderDataPadding
  columnsMask := unifiedDecoderDataColumnsMask
  tagged := unifiedDecoderDataTagged
  offset := unifiedDecoderDataOffset
  prefixTags := unifiedDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
