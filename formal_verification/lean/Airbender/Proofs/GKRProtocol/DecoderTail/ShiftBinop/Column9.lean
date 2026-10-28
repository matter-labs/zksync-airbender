import Airbender.Proofs.GKRProtocol.DecoderTailNormalization
import Airbender.Proofs.GKRProtocol.ShiftPrefixNative.Column9
import Airbender.Data.Decoder.Setup.ShiftBinop

namespace Airbender.Compiler.DecoderTail.ShiftBinop.Column9
open Airbender Airbender.Compiler Airbender.Compiler.ShiftPrefixNative.Column9
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem tail_value (index : Nat) : Data.GKRSetup.ShiftBinop.setupColumn9.get? (524545 + index) = Setup.getFromBlocks suffix index := by
  change Setup.getFromBlocks Data.GKRSetup.ShiftBinop.setupColumn9.blocks.toList (524545 + index) = _
  rw [sourceShape]
  have skipped := Setup.Proofs.skip_blocks originals.flatten suffix index
  rw [prefixLength] at skipped
  exact skipped

noncomputable def targetTail : List Setup.Block :=
  Trace.NativeDecoder.shiftBinopSetup.realRows.columns[9].blocks.toList ++
  Trace.NativeDecoder.shiftBinopSetup.padding.columns[9].blocks.toList

theorem tail_checked : normalizeSetupBlocks suffix = normalizeSetupBlocks targetTail := by rfl

theorem decoder_tail_value (index : Nat) : Data.GKRSetup.ShiftBinop.setupColumn9.get? (524545 + index) = Setup.getFromBlocks targetTail index :=
  (tail_value index).trans ((normalizeSetupBlocks_sound suffix index).symm.trans
    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans
      (normalizeSetupBlocks_sound targetTail index)))

end Airbender.Compiler.DecoderTail.ShiftBinop.Column9
