module
public import Slop.NonVacuous.HashCallers.PooledRow
public import Slop.NonVacuous.HashCallers.Joint
public import Slop.NonVacuous.Blake2GSpan.Span
public import Slop.NonVacuous.Basic
public import Human.Helpers.Delegation.RVMixedMemory
public import Human.Trace.Delegation.RVRequestHashWindows

@[expose] public section

/-! A six-family caller trace issuing a complete reduced G span: 56 ADD/SUB callers `csrrw x0, 0x7C8, x0` at PC
    `4 k` and clock `4 + 4 k` (the block of `PooledRow.lean` rows, facts stated once over the block), fulfilled by the
    span of `Blake2GSpan/From.lean` from the seed of `before` at invocation clocks `5 + 4 k`; one shared memory permutation over
    x0 and the span's cells. The witness that the assumptions of the delegation complete-span caller claims
    (`Human/Trace/Delegation/RVCallerTheorems.lean`) can be met, with the window `(4, 228]`. -/

namespace Airbender.NonVacuous.HashCallers.Pooled
open Trace NonVacuous.Blake2GSpan Delegation.Caller

local notation "P" => babyBearModulus

def callerRow (k : Nat) : Row P PooledFamily := PooledRow.row (4 * k) (4 + 4 * k) (previousOf 0 4 k)

def callerRows : List (Row P PooledFamily) := (List.range 56).map callerRow

theorem mem_rows {row : Row P PooledFamily} (member : row ∈ callerRows) : ∃ k < 56, row = callerRow k := by
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  exact ⟨k, List.mem_range.mp present, rfl⟩

theorem valid {k : Nat} (small : k < 56) : PooledRow.Valid (4 * k) (4 + 4 * k) (previousOf 0 4 k) := by
  refine ⟨by omega, by simp only [timestampBase]; omega, ?_⟩
  unfold previousOf
  split <;> omega

/-- The span's starting state with the caller program in ROM. -/
def before : RV.State := { Blake2GSpan.before with rom := rom 0 fun _ => 0 }

theorem start : Start seed 5 := ⟨inv_mono seed_inv (by omega), rfl, by decide⟩

def machineSteps : List (Cell × MemoryToken P) := (List.range 56).flatMap fun k => x0Steps (4 + 4 * k)

noncomputable def workers : Delegation.MemoryData P := workersFrom seed 5

noncomputable def machine : PooledTrace P where
  rows := callerRows
  rom := ⟨ROM.table keys (romImageRV before keys), Verification.subwordTable (ROM.wordsRV before)⟩
  initial := (callerRow 0).start
  terminal := (callerRow 55).finish
  initialMemory := keys.map seed
  terminalMemory := keys.map (runFinal (runFinal seed machineSteps) (spanSteps seed 5))

noncomputable def data : RVRequestTrace P := ⟨machine, workers, program 0 56⟩

theorem callers : data.callers = data.machine.rows :=
  List.filter_eq_self.mpr fun row member => by
    obtain ⟨k, -, rfl⟩ := mem_rows member
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, PooledRow.selected ..⟩

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by decide : 0 < 56)))

theorem calls : data.calls = (List.range 56).map (requestAt 4) := by
  rw [RVRequestTrace.calls, callers]
  change callerRows.map _ = _
  rw [callerRows, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp, callerRow, PooledRow.request, requestAt]
  congr 3
  omega

theorem checks : RVRequestChecks data where
  constraints row member := by
    obtain ⟨k, small, rfl⟩ := mem_rows member
    exact PooledRow.satisfies (valid small)
  active row member := by
    obtain ⟨k, -, rfl⟩ := mem_rows member
    exact PooledRow.active ..
  states := by
    change ((callerRow 0).start :: ((List.range 56).map callerRow).map Row.finish).Perm
      ((callerRow 55).finish :: ((List.range 56).map callerRow).map Row.start)
    simp only [List.map_map]
    exact chain_perm (start := fun k => (callerRow k).start) (finish := fun k => (callerRow k).finish) 55
      fun k _ => by
        simp only [callerRow]
        rw [PooledRow.finish_start _ _ _ (previousOf 0 4 (k + 1))]
        congr 2
  decoded row member := by
    rw [callers] at member
    obtain ⟨k, small, rfl⟩ := mem_rows member
    refine ⟨⟨k, by simpa [data, program, callerPCs] using small⟩, ?_⟩
    simp only [data, program, callerPCs, List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [Nat.zero_add]
    exact PooledRow.query (4 * k) (4 + 4 * k) (previousOf 0 4 k) (by omega)
  workerConstraints := (accepted_from start).constraints
  workerActive := execute_from
  requests := by
    rw [Delegation.Requests.Matching, calls, RVRequestTrace.fulfillments]
    change Delegation.Requests.Matching _ ((workersFrom seed (4 + 1)).rows.map Delegation.Requests.fulfillment)
    rw [fulfillments]
    exact List.perm_append_comm

theorem accepted : RVRequestAccepted data where
  toRVRequestChecks := checks
  workerMemory := (accepted_from start).matching

theorem shared_accepted : RVSharedMemoryAccepted data where
  toRVRequestChecks := checks
  callerRows := callers
  memory := by
    have first : seed (.register 0) = x0Token (previousOf 0 4 0) := rfl
    obtain ⟨run, untouched⟩ := x0_run (base := seed) (clock := fun k => 4 + 4 * k) 56 first previous_chain
    have edges : callerRows.flatMap (fun row => architecturalSteps row.assignment) =
        (List.range 56).flatMap fun k => x0Edges (previousOf 0 4 k) (4 + 4 * k) := by
      rw [callerRows, List.flatMap_map]
      exact List.flatMap_congr fun k _ => PooledRow.steps ..
    rw [RVRequestTrace.sharedSteps]
    change (keys.map seed ++ (callerRows.flatMap _ ++ (workersFrom seed 5).steps).map Prod.snd).Perm
      (keys.map _ ++ (callerRows.flatMap _ ++ (workersFrom seed 5).steps).map Prod.fst)
    rw [edges]
    refine joint_matching run (fun step member => ?_) (fun c member => untouched c ?_) start
    · obtain ⟨k, -, present⟩ := List.mem_flatMap.mp member
      simp only [x0Steps, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact List.mem_cons_self ..
    · rintro rfl
      exact absurd member (by decide +kernel)

theorem readable : ∀ cell ∈ keys, (cell.readRV before).isSome := by decide +kernel

theorem request_inputs : RVRequestInputs data before (callerPCs 0 56) where
  image := program_image (prefixBytes := fun _ => 0) rfl rfl (by decide)
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem control_start :
    (Cell.register 12).readRV before = some (HashSpan.blakeG true).controlStart := by decide

theorem shared_span_inputs : RVSharedSpanInputs data before (callerPCs 0 56) keys (.blakeG true) where
  publicProgram := request_inputs
  initialization := initial_image readable
  distinct := by decide +kernel
  aligned := by decide +kernel
  tables := rfl
  family := family_from
  controlStart := control_start
  calls := calls_from

/-- The whole span writes in `(4, 228]`. -/
theorem window : data.workers.windowRows 4 228 = data.workers.rows := window_from start (by omega) (by omega)

theorem window_ne : data.workers.windowRows 4 228 ≠ [] := by
  rw [window]
  exact List.ne_nil_of_length_pos (by rw [show data.workers = workersFrom seed 5 from rfl, calls_from]; omega)

/-- The span's worker-only window ABI, read from `before`. -/
theorem window_inputs : Blake2G.RVWindowInputs data.workers before cells true 4 228 where
  memory := ⟨initial_image Blake2GSpan.readable, by decide +kernel, clock_room_from start, invocation_high_from start⟩
  tables := rfl
  family := family_from
  active := active_from
  controlStart := control_start
  prefixComplete := by
    change ((workersFrom seed 5).prefixRows 4).length % 56 = 0
    rw [prefix_from start (by omega)]
    rfl
  calls := by rw [window]; exact calls_from

end Airbender.NonVacuous.HashCallers.Pooled
