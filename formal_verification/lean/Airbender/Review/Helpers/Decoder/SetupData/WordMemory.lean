import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder wordDecoderData from "artifacts/setup/word-memory.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def wordMemorySetup : PackedSetup := {
  width := wordDecoderData.columns.size
  realRows := wordDecoderData
  padding := wordDecoderDataPadding
  columnsMask := wordDecoderDataColumnsMask
  tagged := wordDecoderDataTagged
  offset := wordDecoderDataOffset
  prefixTags := wordDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
