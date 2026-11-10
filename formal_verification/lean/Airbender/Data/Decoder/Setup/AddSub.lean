import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder addSubDecoderData from "artifacts/setup/add-sub.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def addSubSetup : PackedSetup := {
  width := addSubDecoderData.columns.size
  realRows := addSubDecoderData
  padding := addSubDecoderDataPadding
  columnsMask := addSubDecoderDataColumnsMask
  tagged := addSubDecoderDataTagged
  offset := addSubDecoderDataOffset
  prefixTags := addSubDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
