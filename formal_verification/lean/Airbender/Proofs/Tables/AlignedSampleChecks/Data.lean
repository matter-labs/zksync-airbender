import Airbender.Import.PackedSetupEmbed
import Airbender.Proofs.GKRProtocol.PackedSetupSamples
import Airbender.Proofs.Tables.ReferenceControl

namespace Airbender.Verification.AlignedSampleChecks
open Airbender Airbender.Compiler PackedSetupEquality PackedSetupSamples
set_option warningAsError true
set_option Elab.async false

import_setup_code_capture from "artifacts/setup/jump-branch.json" [
  conditionalBlocks := region 31 column 1 block_start 0 block_count 47 packed_bytes 0
]

def conditional : Request := ⟨conditionalBlocks, 128, fun index => conditionalValue (index.val * 32768)⟩

def conditionalRequests : List Request := [conditional]

import_setup_code_capture from "artifacts/setup/shift-binop.json" [
  positionBlocks := region 9 column 0 block_start 0 block_count 4 packed_bytes 0
]

def position : Request := ⟨positionBlocks, 8, fun index => index.val / 2⟩

def positionRequests : List Request := [position]

end Airbender.Verification.AlignedSampleChecks
