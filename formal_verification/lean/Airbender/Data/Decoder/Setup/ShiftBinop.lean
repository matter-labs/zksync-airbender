import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Import.SetupDecoderEmbed

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000

import_setup_decoder shiftDecoderData from "artifacts/setup/shift-binop.json"

/-- Actual retained native decoder with its exported packing and offsets. -/
def shiftBinopSetup : PackedSetup := {
  width := shiftDecoderData.columns.size
  realRows := shiftDecoderData
  padding := shiftDecoderDataPadding
  columnsMask := shiftDecoderDataColumnsMask
  tagged := shiftDecoderDataTagged
  offset := shiftDecoderDataOffset
  prefixTags := shiftDecoderDataPrefixTags
}

end Airbender.Trace.NativeDecoder
