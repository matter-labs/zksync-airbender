import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder subwordDecoderData from "artifacts/setup/subword-memory.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def subwordSetup : PackedSetup := {
  width := subwordDecoderData.columns.size
  realRows := subwordDecoderData
  padding := subwordDecoderDataPadding
  columnsMask := subwordDecoderDataColumnsMask
  tagged := subwordDecoderDataTagged
  offset := subwordDecoderDataOffset
  prefixTags := subwordDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
