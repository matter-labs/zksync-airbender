import Airbender.Proofs.GKRProtocol.HelperProjectionChecks
import Airbender.Proofs.GKRProtocol.MemorySymbols

namespace Airbender.Compiler.HelperHistoryProjectionChecks
set_option warningAsError true

def projectedPairs (bank : WireBank n) (pairs : List (GKRAddress × GKRAddress)) :=
  (List.range pairs.length).map (fun index =>
    let pair := (pairs[index]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0)
    (bank.address (bank.placement pair.1), bank.address (bank.placement pair.2)))

theorem projectedPairs_eq (bank : WireBank n) (pairs : List (GKRAddress × GKRAddress))
    (checked : bank.inputCheck (pairs.flatMap (fun pair => [pair.1, pair.2])) = true) :
    projectedPairs bank pairs = pairs := by
  calc
    _ = (List.range pairs.length).map (fun index =>
        (pairs[index]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0)) := by
      apply List.map_congr_left
      intro index member
      have inside := List.mem_range.mp member
      have seen : (pairs[index]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0) ∈ pairs := by
        simp [inside]
      have lowMember : ((pairs[index]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0)).1 ∈
          pairs.flatMap (fun pair => [pair.1, pair.2]) :=
        List.mem_flatMap.mpr ⟨_, seen, by simp⟩
      have highMember : ((pairs[index]?).getD (.BaseLayerMemory 0, .BaseLayerMemory 0)).2 ∈
          pairs.flatMap (fun pair => [pair.1, pair.2]) :=
        List.mem_flatMap.mpr ⟨_, seen, by simp⟩
      exact Prod.ext
        ((addressEqual_iff _ _).mp (List.all_eq_true.mp checked _ lowMember))
        ((addressEqual_iff _ _).mp (List.all_eq_true.mp checked _ highMember))
    _ = pairs := by simp only [List.map_range_getD]

end Airbender.Compiler.HelperHistoryProjectionChecks
