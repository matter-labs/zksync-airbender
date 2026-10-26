import Airbender.Proofs.GKRProtocol.ChunkSpans

namespace Airbender.Compiler
set_option warningAsError true

theorem block_partitions_length (sources : List Setup.Block) (targets : List (List Setup.Block))
    (checked : List.Forall₂ (fun source target =>
      (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets) :
    (sources.map Setup.Block.length).sum = (targets.flatten.map Setup.Block.length).sum := by
  induction checked with
  | nil => rfl
  | @cons source target rest tail agreement remaining ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append, List.sum_append]
    rw [agreement.1, ih]

theorem block_partitions_chunk_agreement (sources : List Setup.Block) (targets : List (List Setup.Block))
    (checked : List.Forall₂ (fun source target =>
      (target.map Setup.Block.length).sum = source.length ∧ blockTargetsFollow source 0 target) sources targets) :
    blockChunkAgreement sources targets.flatten :=
  ⟨block_partitions_length sources targets checked, block_partitions_agree sources targets checked⟩

end Airbender.Compiler
