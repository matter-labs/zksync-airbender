import Airbender.Proofs.GKRProtocol.DecoderTailNormalization
import Airbender.Data.GKRSetup.AddSub
import Airbender.Import.GKRProtocol.BlockCoverageImport
import Airbender.Review.Helpers.Decoder.SetupData.AddSub

namespace Airbender.Compiler.DecoderTail.AddSub.Column7
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part prefixBlocks from Data.GKRSetup.AddSub.setupColumn7 start 0 stop 0
column_blocks_part suffix from Data.GKRSetup.AddSub.setupColumn7 start 0 stop 2

theorem sourceShape : Data.GKRSetup.AddSub.setupColumn7.blocks.toList = prefixBlocks ++ suffix := by rfl

theorem prefixLength : (prefixBlocks.map Setup.Block.length).sum = 0 := by decide +kernel

theorem tail_value (index : Nat) : Data.GKRSetup.AddSub.setupColumn7.get? (0 + index) = Setup.getFromBlocks suffix index := by
  change Setup.getFromBlocks Data.GKRSetup.AddSub.setupColumn7.blocks.toList (0 + index) = _
  rw [sourceShape]
  have skipped := Setup.Proofs.skip_blocks prefixBlocks suffix index
  rw [prefixLength] at skipped
  exact skipped

noncomputable def targetTail : List Setup.Block :=
  Trace.NativeDecoder.addSubSetup.realRows.columns[7].blocks.toList ++
  Trace.NativeDecoder.addSubSetup.padding.columns[7].blocks.toList

theorem tail_checked : normalizeSetupBlocks suffix = normalizeSetupBlocks targetTail := by rfl

theorem decoder_tail_value (index : Nat) : Data.GKRSetup.AddSub.setupColumn7.get? (0 + index) = Setup.getFromBlocks targetTail index :=
  (tail_value index).trans ((normalizeSetupBlocks_sound suffix index).symm.trans
    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans
      (normalizeSetupBlocks_sound targetTail index)))

end Airbender.Compiler.DecoderTail.AddSub.Column7
