import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder mulDivDecoderData from "artifacts/setup/mul-div.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def mulDivSetup : PackedSetup := {
  width := mulDivDecoderData.columns.size
  realRows := mulDivDecoderData
  padding := mulDivDecoderDataPadding
  columnsMask := mulDivDecoderDataColumnsMask
  tagged := mulDivDecoderDataTagged
  offset := mulDivDecoderDataOffset
  prefixTags := mulDivDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
