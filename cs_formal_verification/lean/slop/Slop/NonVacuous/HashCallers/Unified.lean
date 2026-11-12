module
public import Slop.NonVacuous.FamilyCallers.Block
public import Slop.NonVacuous.HashCallers.Joint
public import Slop.NonVacuous.Blake2GSpan.Span
public import Slop.NonVacuous.Basic
public import Human.Trace.UnifiedReduced.RVJointHashWindows

@[expose] public section

/-! A caller-only unified trace issuing a complete reduced G span: 56 callers `csrrw x0, 0x7C8, x0` at PC `4 k` and
    clock `4 + 4 k`, fulfilled by the span of `Blake2GSpan/From.lean` from the seed of `before` at invocation clocks
    `5 + 4 k` (x10 = 0x400000, x11 = 0x400040, x12 = 128, RAM a byte pattern; ROM the caller instruction). One joint memory
    permutation over x0 and the span's cells. The witness that the assumptions of the unified complete-span caller
    claims (`Human/Trace/UnifiedReduced/RVCallerTheorems.lean`) can be met, with the window `(4, 228]`. -/

namespace Airbender.NonVacuous.HashCallers.Unified
open Trace NonVacuous.Blake2GSpan UnifiedReduced.Caller FamilyCallers.Block
open FamilyCallers (callerPCs)

local notation "P" => babyBearModulus

/-- The span's starting state with the caller program in ROM. -/
def before : RV.State := { Blake2GSpan.before with rom := FamilyCallers.rom .blakeG 0 fun _ => 0 }

theorem start : Start seed 5 := ⟨inv_mono seed_inv (by omega), rfl, by decide⟩

theorem room : Room 0 4 0 56 := ⟨by omega, by decide, by omega⟩

/-- The callers' x0 steps. -/
def machineSteps : List (Cell × MemoryToken P) := (List.range 56).flatMap fun k => x0Steps (4 + 4 * k)

noncomputable def workers : Delegation.MemoryData P := workersFrom seed 5

noncomputable def machine : UnifiedTrace P where
  rows := callerRows .blakeG 0 4 0 56
  rom := UnifiedReduced.Setup.tableRV before
  initial := (callerRow .blakeG 0 4 0 0).start
  terminal := (callerRow .blakeG 0 4 0 55).finish
  initialMemory := keys.map seed
  terminalMemory := keys.map (runFinal (runFinal seed machineSteps) (spanSteps seed 5))

noncomputable def data : RVRequestTrace P := ⟨machine, workers, FamilyCallers.program .blakeG 0 56⟩

theorem callers : data.callers = data.machine.rows := filter_selected

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by decide : 0 < 56)))

theorem checks : RVRequestChecks data where
  constraints := satisfies room before
  active := active
  states := states 55
  decoded row member := decoded room row (by rw [callers] at member; exact member)
  workerConstraints := (accepted_from start).constraints
  workerActive := execute_from
  requests := by
    rw [Delegation.Requests.Matching, RVRequestTrace.calls, RVRequestTrace.fulfillments, callers]
    change Delegation.Requests.Matching ((callerRows .blakeG 0 4 0 56).map fun row => request row.assignment)
      (((List.range 56).map (rowFrom seed (4 + 1))).map Delegation.Requests.fulfillment)
    rw [requests, fulfillments (row := rowFrom seed (4 + 1)) (fun _ => rfl) (invocation_raw seed (4 + 1))]
    exact List.perm_append_comm

theorem x0_run_seed : seed (.register 0) = x0Token (previousOf 0 4 0) := rfl

theorem accepted : RVMixedMemoryAccepted data [] where
  toRVRequestChecks := checks
  ordinaryDecoded row member notCaller := absurd (by rw [callers]; exact member) notCaller
  memory := by
    obtain ⟨run, untouched⟩ := x0_run (base := seed) (clock := fun k => 4 + 4 * k) 56 x0_run_seed previous_chain
    rw [RVRequestTrace.mixedSteps]
    change (keys.map seed ++ ((callerRows .blakeG 0 4 0 56).flatMap _ ++ (workersFrom seed 5).steps).map Prod.snd).Perm
      (keys.map _ ++ ((callerRows .blakeG 0 4 0 56).flatMap _ ++ (workersFrom seed 5).steps).map Prod.fst)
    rw [FamilyCallers.Block.edges]
    refine joint_matching keys_nodup (fun _ => List.mem_cons_of_mem _) run (fun step member => ?_)
      (fun c member => untouched c ?_) (inside_from start) (blocks_from start).1
    · obtain ⟨k, -, present⟩ := List.mem_flatMap.mp member
      simp only [x0Steps, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact List.mem_cons_self ..
    · rintro rfl
      exact absurd member (by decide +kernel)

theorem readable : ∀ cell ∈ keys, (cell.readRV before).isSome := by decide +kernel

theorem initialization : initialImageRV before keys = some data.machine.initialMemory := initial_image readable

theorem request_inputs : RVRequestInputs data before (callerPCs 0 56) where
  image := FamilyCallers.program_image (prefixBytes := fun _ => 0) rfl rfl (by decide)
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem control_start :
    (Cell.register 12).readRV before = some (Delegation.Caller.HashSpan.blakeG true).controlStart := by decide

theorem shared_span_inputs : RVSharedSpanInputs data before (callerPCs 0 56) keys (.blakeG true) where
  toRVRequestInputs := request_inputs
  tables := rfl
  family := family_from
  controlStart := control_start
  calls := calls_from
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel

/-- The whole span writes in `(4, 228]`. -/
theorem window : data.workers.windowRows 4 228 = data.workers.rows := window_from start (by omega) (by omega)

theorem window_ne : data.workers.windowRows 4 228 ≠ [] := by
  rw [window]
  exact List.ne_nil_of_length_pos (by rw [show data.workers = workersFrom seed 5 from rfl, calls_from]; omega)

theorem joint_inputs : RVJointHashWindowInputs data before (callerPCs 0 56) keys (.blakeG true) 4 228 where
  publicProgram := request_inputs
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  family := family_from
  controlStart := control_start
  prefixScope := by
    change ((workersFrom seed 5).prefixRows 4).length % 56 = 0
    rw [prefix_from start (by omega)]
    rfl
  calls := by rw [window]; exact calls_from

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

end Airbender.NonVacuous.HashCallers.Unified
