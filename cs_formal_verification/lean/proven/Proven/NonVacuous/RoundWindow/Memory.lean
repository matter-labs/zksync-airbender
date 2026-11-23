module
public import Proven.NonVacuous.RoundWindow.Rows

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine HashCallers
set_option warningAsError true

private theorem unrolled_edges :
    unrolledSteps unrolledTrace =
      (List.range 10).flatMap (fun index => x0Edges (previousOf 0 4 index) (4 + 4 * index)) := by
  change unrolledRows.flatMap _ = _
  rw [unrolledRows, List.flatMap_map]
  apply List.flatMap_congr
  intro index _
  change Delegation.Caller.architecturalSteps (unrolledRow index).assignment = _
  exact unrolled_steps index

private theorem unified_edges :
    unifiedSteps unifiedTrace =
      (List.range 10).flatMap (fun index => x0Edges (previousOf 0 4 index) (4 + 4 * index)) := by
  exact FamilyCallers.Block.edges

private theorem worker_edges :
    workers.steps = (Blake2RoundSpan.workersFrom Blake2RoundSpan.seed 5).steps := by
  change (Blake2RoundSpan.workersFrom Blake2RoundSpan.seed 5).steps ++ [] = _
  exact List.append_nil _

private theorem machine_run :
    (List.range 10).flatMap (fun index => x0Edges (previousOf 0 4 index) (4 + 4 * index)) =
        runEdges Blake2RoundSpan.seed machineSteps ∧
      ∀ cell ∈ Blake2RoundSpan.cells,
        runFinal Blake2RoundSpan.seed machineSteps cell = Blake2RoundSpan.seed cell := by
  have first : Blake2RoundSpan.seed (.register 0) = x0Token (previousOf 0 4 0) := by decide +kernel
  obtain ⟨edges, untouched⟩ := x0_run (base := Blake2RoundSpan.seed)
    (clock := fun index => 4 + 4 * index) 10 first previous_chain
  refine ⟨edges, fun cell member => ?_⟩
  have separate : cell ≠ .register 0 := by
    rintro rfl
    exact absurd member (by decide +kernel)
  exact untouched cell separate

private theorem memory_matching :
    (keys.map Blake2RoundSpan.seed ++
      (((List.range 10).flatMap (fun index => x0Edges (previousOf 0 4 index) (4 + 4 * index))) ++
        (Blake2RoundSpan.workersFrom Blake2RoundSpan.seed 5).steps).map Prod.snd).Perm
      (keys.map (runFinal (runFinal Blake2RoundSpan.seed machineSteps)
          (Blake2RoundSpan.spanSteps Blake2RoundSpan.seed 5)) ++
        (((List.range 10).flatMap (fun index => x0Edges (previousOf 0 4 index) (4 + 4 * index))) ++
          (Blake2RoundSpan.workersFrom Blake2RoundSpan.seed 5).steps).map Prod.fst) := by
  obtain ⟨edges, untouched⟩ := machine_run
  refine joint_matching RoundCallers.keys_nodup (fun _ => List.mem_cons_of_mem _) edges
    (fun step member => ?_) untouched Blake2RoundSpan.inside_from (Blake2RoundSpan.blocks_from start).1
  obtain ⟨index, _, present⟩ := List.mem_flatMap.mp member
  simp only [x0Steps, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> exact List.mem_cons_self ..

/-- The unrolled callers and ten round workers share one initialized memory permutation. -/
theorem unrolled_memory :
    (unrolledTrace.initialMemory ++ (unrolledSteps unrolledTrace ++ workers.steps).map Prod.snd).Perm
      (unrolledTrace.terminalMemory ++ (unrolledSteps unrolledTrace ++ workers.steps).map Prod.fst) := by
  rw [unrolled_edges, worker_edges]
  exact memory_matching

/-- The unified callers and ten round workers share the same initialized memory permutation. -/
theorem unified_memory :
    (unifiedTrace.initialMemory ++ (unifiedSteps unifiedTrace ++ workers.steps).map Prod.snd).Perm
      (unifiedTrace.terminalMemory ++ (unifiedSteps unifiedTrace ++ workers.steps).map Prod.fst) := by
  rw [unified_edges, worker_edges]
  exact memory_matching

end Airbender.NonVacuous.RoundWindow
