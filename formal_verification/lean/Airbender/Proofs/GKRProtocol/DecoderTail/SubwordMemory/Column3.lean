import Airbender.Proofs.GKRProtocol.DecoderTailNormalization
import Airbender.Proofs.GKRProtocol.SubwordPrefixNative.Column3
import Airbender.Review.Helpers.Decoder.SetupData.Subword

namespace Airbender.Compiler.DecoderTail.SubwordMemory.Column3
open Airbender Airbender.Compiler Airbender.Compiler.SubwordPrefixNative.Column3
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem tail_value (index : Nat) : Data.GKRSetup.SubwordMemory.setupColumn3.get? (13238273 + index) = Setup.getFromBlocks suffix index := by
  change Setup.getFromBlocks Data.GKRSetup.SubwordMemory.setupColumn3.blocks.toList (13238273 + index) = _
  rw [sourceShape]
  have skipped := Setup.Proofs.skip_blocks originals.flatten suffix index
  rw [prefixLength] at skipped
  exact skipped

noncomputable def targetTail : List Setup.Block :=
  Trace.NativeDecoder.subwordSetup.realRows.columns[3].blocks.toList ++
  Trace.NativeDecoder.subwordSetup.padding.columns[3].blocks.toList

theorem tail_checked : normalizeSetupBlocks suffix = normalizeSetupBlocks targetTail := by rfl

theorem decoder_tail_value (index : Nat) : Data.GKRSetup.SubwordMemory.setupColumn3.get? (13238273 + index) = Setup.getFromBlocks targetTail index :=
  (tail_value index).trans ((normalizeSetupBlocks_sound suffix index).symm.trans
    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans
      (normalizeSetupBlocks_sound targetTail index)))

end Airbender.Compiler.DecoderTail.SubwordMemory.Column3
