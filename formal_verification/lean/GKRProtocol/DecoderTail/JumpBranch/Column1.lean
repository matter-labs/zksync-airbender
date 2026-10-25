import GKRProtocol.DecoderTailNormalization
import Airbender.Data.GKRSetup.JumpBranch
import GKRProtocol.BlockCoverageImport
import Airbender.Review.Helpers.Decoder.SetupData.JumpBranch

namespace Airbender.Compiler.DecoderTail.JumpBranch.Column1
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

column_blocks_part prefixBlocks from Data.GKRSetup.JumpBranch.setupColumn1 start 0 stop 52
column_blocks_part suffix from Data.GKRSetup.JumpBranch.setupColumn1 start 52 stop 55

column_parts_cover coverage from Data.GKRSetup.JumpBranch.setupColumn1 parts [prefixBlocks, suffix]

theorem sourceShape : Data.GKRSetup.JumpBranch.setupColumn1.blocks.toList = prefixBlocks ++ suffix := by
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using coverage

theorem prefixLength : (prefixBlocks.map Setup.Block.length).sum = 4456448 := by decide +kernel

theorem tail_value (index : Nat) : Data.GKRSetup.JumpBranch.setupColumn1.get? (4456448 + index) = Setup.getFromBlocks suffix index := by
  change Setup.getFromBlocks Data.GKRSetup.JumpBranch.setupColumn1.blocks.toList (4456448 + index) = _
  rw [sourceShape]
  have skipped := Setup.Proofs.skip_blocks prefixBlocks suffix index
  rw [prefixLength] at skipped
  exact skipped

noncomputable def targetTail : List Setup.Block :=
  Trace.NativeDecoder.jumpBranchSetup.realRows.columns[1].blocks.toList ++
  Trace.NativeDecoder.jumpBranchSetup.padding.columns[1].blocks.toList

theorem tail_checked : normalizeSetupBlocks suffix = normalizeSetupBlocks targetTail := by rfl

theorem decoder_tail_value (index : Nat) : Data.GKRSetup.JumpBranch.setupColumn1.get? (4456448 + index) = Setup.getFromBlocks targetTail index :=
  (tail_value index).trans ((normalizeSetupBlocks_sound suffix index).symm.trans
    ((congrArg (fun blocks => Setup.getFromBlocks blocks index) tail_checked).trans
      (normalizeSetupBlocks_sound targetTail index)))

end Airbender.Compiler.DecoderTail.JumpBranch.Column1
