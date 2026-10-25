import GKRProtocol.DecoderTailNormalization
import GKRProtocol.UnifiedAllPrefix.Column2
import Airbender.Review.Helpers.Decoder.SetupData.Unified

namespace Airbender.Compiler.DecoderTail.Unified.Column2
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedAllPrefix.Column2
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem tail_value (index : Nat) :
    Data.GKRSetup.Unified.setupColumn2.get? (2097537 + index) =
      Setup.getFromBlocks (extra ++ suffix) index := by
  apply column_tail_value _ originals.flatten regionBlocks extra suffix 2097537 sourceShape
  · rw [originalLength, List.map_append, List.sum_append, regionTotal]
    decide +kernel
  · intro position
    exact (block_chunks_agree originals targets chunksChecked position).trans
      (congrArg (fun blocks => Setup.getFromBlocks blocks position) targetShape).symm
  · exact regionTotal

noncomputable def targetTail : List Setup.Block :=
  Trace.NativeDecoder.unifiedSetup.realRows.columns[2].blocks.toList ++
  Trace.NativeDecoder.unifiedSetup.padding.columns[2].blocks.toList

theorem tail_checked : normalizeDecoderTail (extra ++ suffix) = normalizeDecoderTail targetTail := by
  rfl

theorem decoder_tail_value (index : Nat) :
    Data.GKRSetup.Unified.setupColumn2.get? (2097537 + index) = Setup.getFromBlocks targetTail index :=
  (tail_value index).trans ((normalize_decoder_tail_sound (extra ++ suffix) index).symm.trans
    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans
      (normalize_decoder_tail_sound targetTail index)))

end Airbender.Compiler.DecoderTail.Unified.Column2
