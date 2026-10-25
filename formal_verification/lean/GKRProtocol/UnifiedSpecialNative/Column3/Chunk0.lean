import GKRProtocol.UnifiedSpecialParts.Column3.Chunk0.Part0
import GKRProtocol.ChunkLengths

namespace Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def sources : List Setup.Block := [source0, source1, source2]

noncomputable def targets : List (List Setup.Block) := [target0, target1, target2]

noncomputable def target : List Setup.Block := targets.flatten

theorem sourcesAgree : original = sources := by rfl

theorem spansChecked : List.Forall₂ (fun source target => (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets :=
  List.Forall₂.cons (⟨length0, follows0⟩) (List.Forall₂.cons (⟨length1, follows1⟩) (List.Forall₂.cons (⟨length2, follows2⟩) (List.Forall₂.nil)))

theorem chunkAgreement : blockChunkAgreement original target := by
  rw [sourcesAgree]
  exact block_partitions_chunk_agreement sources targets spansChecked

end Airbender.Compiler.UnifiedSpecialChunks.Column3.Chunk0
