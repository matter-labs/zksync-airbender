module
public import Slop.NonVacuous.Blake2GSpan.From

@[expose] public section

/-! The joint memory matching of a machine path followed by a complete G span: the machine's steps are a run over
    x0 and the span's cells from the seed, the span starts from a memory agreeing with that run's end on its cells,
    and the whole is one sequential run over `x0 :: cells` (`SequentialRun.lean`). -/

namespace Airbender.NonVacuous.HashCallers
open Trace NonVacuous.Blake2GSpan

local notation "P" => babyBearModulus

/-- The joint cells: x0 and the span's cells. -/
def keys : List Cell := .register 0 :: cells

theorem keys_nodup : keys.Nodup := by decide +kernel

/-- The machine's edges then the span's steps match the seed of `keys` against the final run's values. -/
theorem joint_matching {seed m0 : Memory} {t0 : Nat} {machine : List (Cell × MemoryToken P)}
    {edges : List (MemoryToken P × MemoryToken P)} (run : edges = runEdges seed machine)
    (inside : ∀ step ∈ machine, step.1 ∈ keys) (agree : ∀ c ∈ cells, runFinal seed machine c = m0 c)
    (start : Start m0 t0) :
    (keys.map seed ++ (edges ++ (workersFrom m0 t0).steps).map Prod.snd).Perm
      (keys.map (runFinal (runFinal seed machine) (spanSteps m0 t0)) ++
        (edges ++ (workersFrom m0 t0).steps).map Prod.fst) := by
  have whole := run_matching keys_nodup seed (steps := machine ++ spanSteps m0 t0) fun step member => by
    rcases List.mem_append.mp member with early | late
    · exact inside step early
    · exact List.mem_cons_of_mem _ (inside_from start step late)
  have same := (run_congr (mem := runFinal seed machine) (other := m0) (steps := spanSteps m0 t0) fun key member => by
    obtain ⟨step, present, rfl⟩ := List.mem_map.mp member
    exact agree _ (inside_from start step present)).1
  rw [runEdges_append, runFinal_append, same, ← (blocks_from start).1, ← run] at whole
  simpa only [Delegation.MemoryData.steps, workersFrom] using whole

end Airbender.NonVacuous.HashCallers
