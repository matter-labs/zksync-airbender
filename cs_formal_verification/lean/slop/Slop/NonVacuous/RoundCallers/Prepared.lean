module
public import Slop.NonVacuous.RoundCallers.Joint
public import Slop.NonVacuous.FamilyCallers.Block
public import Slop.NonVacuous.Basic
public import Slop.WitnessCheck
public import Slop.KernelRfl
public import Human.Trace.UnifiedReduced.RVPreparedRoundWindows

@[expose] public section

/-! A prepared unified caller trace issuing a complete extended-round span (flags 0): `lui x12, 0x80` at PC 0 (clock
    4, the preparation `hashPreparation (.blakeRound 0)`, x12 = 0x80000), then ten callers `csrrw x0, 0x7C7, x0` at
    PC `4 + 4 k` and clock `8 + 4 k`, fulfilled by the ten-round span of `Blake2RoundSpan/From.lean` invoked at
    `9 + 4 k`, whose first round reads x12 as the preparation wrote it. One joint memory permutation over x0 and the
    span's cells. The witness that the assumptions of the prepared extended-round caller claims
    (`Human/Trace/UnifiedReduced/RVCallerTheorems.lean`) can be met, with the window and controller region `(8, 48]`. The one preparation row is checked by one kernel
    evaluation (`Slop/WitnessCheck.lean`); the callers and the span are generic (`FamilyCallers/Block.lean`,
    `Blake2RoundSpan/From.lean`). -/

namespace Airbender.NonVacuous.RoundCallers.Prepared
open Trace UnifiedReduced.Caller Verification FamilyCallers.Block
open HashCallers (x0Token x0Steps x0Edges x0_run previousOf previous_chain fulfillments)
open FamilyCallers (callerPCs)
open Blake2RoundSpan (Start inv_mono inv_control workersFrom rowFrom spanSteps inside_from blocks_from invocation_raw
  row_mem_from write_time_from accepted_from execute_from family_from calls_from prefix_from window_from)

local notation "P" => babyBearModulus

/-- `lui x12, 0x80` (`0x00080637`, bytes `37 06 08 00`). -/
def prepBytes (a : Nat) : BitVec 8 := if a = 0 then 0x37 else if a = 1 then 0x06 else if a = 2 then 0x08 else 0x00

/-- The span's starting state with the preparation at ROM address 0 and the callers after it. -/
def before : RV.State := { Blake2RoundSpan.before with rom := FamilyCallers.rom .blakeRound 4 prepBytes }

/-- The preparation row at PC 0 and clock 4: rd = x12 (columns 7, 44), immediate high limb 8 (9) and result 0x80000
    (51), the ADD selector (11); the second port reads x0 as the first left it (clock 4, column 40); the destination
    port reads x12's seed 0x80000 (49). -/
def prepColumn (v : Nat) : Nat :=
  if v = 2 then 4 else if v = 30 then 4 else if v = 40 then 4 else if v = 32 then 8
  else if v = 4 then 1 else if v = 11 then 1 else if v = 123 then 1 else if v = 124 then 1 else if v = 125 then 1
  else if v = 7 then 12 else if v = 44 then 12 else if v = 9 then 8 else if v = 51 then 8 else if v = 49 then 8
  else 0

def prepAssignment (v : Nat) : ZMod P := (prepColumn v : ZMod P)

def prep : Row P UnifiedFamily := ⟨.machine, prepAssignment⟩

noncomputable def setupChecked : CheckedTable (ZMod P) := staticChecked (UnifiedReduced.Setup.tableRV before) rfl

noncomputable def checkedTables : List (CheckedTable (ZMod P)) :=
  List.replicate 13 range16Checked ++ List.replicate 5 setupChecked

theorem lookup_tables : (FlatOperation.lookups (UnifiedReduced.importedConstraints
    (UnifiedReduced.Setup.tableRV (p := P) before))).map Lookup.table = checkedTables.map CheckedTable.table := rfl

theorem timestamp_tables : (FlatOperation.lookups (UnifiedReduced.importedConstraintsTimestampLookups (p := P))).map
    Lookup.table = (List.replicate 8 timestampChecked).map CheckedTable.table := rfl

theorem prep_satisfies : FlatOperation.ConstraintsHoldFlat (environment prepAssignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV before)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl)) (holds_of_checkOps timestamp_tables (by kernel_rfl))

/-- x12 as the preparation leaves it: 0x80000, written at clock 6. -/
def x12Token : MemoryToken P :=
  writeToken UnifiedReduced.importedConstraintsTraceColumns prepAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]

/-- The preparation's steps: x0 refreshed at clocks 4 and 5, x12 written. -/
def prepSteps : List (Cell × MemoryToken P) := [(.register 0, x0Token 4), (.register 0, x0Token 5), (.register 12, x12Token)]

theorem prep_edges : (machinePorts prep).toList.map (fun port =>
    (readToken prep.assignment port, writeToken prep.columns prep.assignment port)) =
      runEdges Blake2RoundSpan.seed prepSteps := by
  decide +kernel

/-- The span's start: the seed with x12 as prepared. -/
def m0 : Blake2GSpan.Memory := Function.update Blake2RoundSpan.seed (.register 12) x12Token

theorem start : Start m0 9 :=
  ⟨inv_control (inv_mono Blake2RoundSpan.seed_inv (by omega)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel), rfl, by decide⟩

theorem room : Room 4 8 5 10 := ⟨by omega, by decide, by omega⟩

def machineSteps : List (Cell × MemoryToken P) := prepSteps ++ (List.range 10).flatMap fun k => x0Steps (8 + 4 * k)

noncomputable def workers : Delegation.MemoryData P := workersFrom m0 9

noncomputable def machine : UnifiedTrace P where
  rows := prep :: callerRows .blakeRound 4 8 5 10
  rom := UnifiedReduced.Setup.tableRV before
  initial := prep.start
  terminal := (callerRow .blakeRound 4 8 5 9).finish
  initialMemory := keys.map Blake2RoundSpan.seed
  terminalMemory := keys.map (runFinal (runFinal Blake2RoundSpan.seed machineSteps) (spanSteps m0 9))

/-- The ordinary program: the preparation. -/
def ordinary : List UnifiedReduced.RVProgramEntry := [⟨0, 0x00080637#32, ⟨.machine, 0, 0, 12, ⟨0, 8⟩, 1, 0⟩⟩]

noncomputable def data : RVRequestTrace P := ⟨machine, workers, FamilyCallers.program .blakeRound 4 10⟩

theorem callers : data.callers = callerRows .blakeRound 4 8 5 10 := by
  simp only [RVRequestTrace.callers, data, machine]
  rw [List.filter_cons_of_neg (by decide +kernel)]
  exact filter_selected

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by decide : 0 < 10)))

theorem checks : RVRequestChecks data where
  constraints row member := by
    rcases List.mem_cons.mp member with rfl | caller
    · exact prep_satisfies
    · exact satisfies room before row caller
  active row member := by
    rcases List.mem_cons.mp member with rfl | caller
    · exact Nat.cast_one
    · exact active row caller
  states := by
    have first : prep.finish = (callerRow .blakeRound 4 8 5 0).start := by kernel_rfl
    change (prep.start :: prep.finish :: (callerRows .blakeRound 4 8 5 10).map Row.finish).Perm
      ((callerRow .blakeRound 4 8 5 9).finish :: prep.start :: (callerRows .blakeRound 4 8 5 10).map Row.start)
    rw [first]
    exact ((states 9).cons _).trans (List.Perm.swap _ _ _)
  decoded row member := decoded room row (by rw [callers] at member; exact member)
  workerConstraints := (accepted_from start).constraints
  workerActive := execute_from
  requests := by
    rw [Delegation.Requests.Matching, RVRequestTrace.calls, RVRequestTrace.fulfillments, callers]
    change Delegation.Requests.Matching ((callerRows .blakeRound 4 8 5 10).map fun row => request row.assignment)
      (((List.range 10).map (rowFrom m0 (8 + 1))).map Delegation.Requests.fulfillment)
    rw [requests, fulfillments (row := rowFrom m0 (8 + 1)) (fun _ => rfl) (invocation_raw m0 (8 + 1))]
    exact List.perm_append_comm

/-- The machine's edges are the run of its steps from the seed; the run leaves the span's cells as `m0`. -/
theorem machine_run :
    runEdges Blake2RoundSpan.seed prepSteps ++
        (List.range 10).flatMap (fun k => x0Edges (previousOf 5 8 k) (8 + 4 * k)) =
      runEdges Blake2RoundSpan.seed machineSteps ∧
      ∀ c ∈ Blake2RoundSpan.cells, runFinal Blake2RoundSpan.seed machineSteps c = m0 c := by
  have first : runFinal Blake2RoundSpan.seed prepSteps (.register 0) = x0Token (previousOf 5 8 0) := by decide +kernel
  obtain ⟨run, untouched⟩ :=
    x0_run (base := runFinal Blake2RoundSpan.seed prepSteps) (clock := fun k => 8 + 4 * k) 10 first previous_chain
  refine ⟨by rw [machineSteps, runEdges_append, run], fun c member => ?_⟩
  have x0 : c ≠ .register 0 := by
    rintro rfl
    exact absurd member (by decide +kernel)
  rw [machineSteps, runFinal_append, untouched c x0]
  simp only [prepSteps, runFinal, m0]
  by_cases same : c = .register 12
  · subst same
    simp only [Function.update_self]
  · rw [Function.update_of_ne same, Function.update_of_ne same, Function.update_of_ne x0, Function.update_of_ne x0]

theorem accepted : RVMixedMemoryAccepted data ordinary where
  toRVRequestChecks := checks
  ordinaryDecoded row member notCaller := by
    rcases List.mem_cons.mp member with rfl | caller
    · exact ⟨⟨0, by decide⟩, by kernel_rfl⟩
    · rw [callers] at notCaller
      exact absurd caller notCaller
  memory := by
    obtain ⟨run, agree⟩ := machine_run
    rw [RVRequestTrace.mixedSteps]
    change (keys.map Blake2RoundSpan.seed ++
        ((prep :: callerRows .blakeRound 4 8 5 10).flatMap _ ++ (workersFrom m0 9).steps).map Prod.snd).Perm
      (keys.map _ ++ ((prep :: callerRows .blakeRound 4 8 5 10).flatMap _ ++ (workersFrom m0 9).steps).map Prod.fst)
    rw [List.flatMap_cons, prep_edges, edges]
    refine joint_matching keys_nodup (fun _ => List.mem_cons_of_mem _) run.symm (fun step member => ?_) agree
      inside_from (blocks_from start).1
    rcases List.mem_append.mp member with early | late
    · simp only [prepSteps, List.mem_cons, List.not_mem_nil, or_false] at early
      rcases early with rfl | rfl | rfl <;> decide +kernel
    · obtain ⟨k, -, present⟩ := List.mem_flatMap.mp late
      simp only [x0Steps, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact List.mem_cons_self ..

theorem readable : ∀ cell ∈ keys, (cell.readRV before).isSome := by decide +kernel

theorem initialization : initialImageRV before keys = some data.machine.initialMemory := initial_image readable

theorem request_inputs : RVRequestInputs data before (callerPCs 4 10) where
  image := FamilyCallers.program_image (prefixBytes := prepBytes) rfl rfl (by decide)
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem ordinary_image : rvProgramImageWith UnifiedReduced.rvDecoderFields before [0] = some ordinary := by kernel_rfl

/-- The preparation decodes to the extended-round span's entry control literal. -/
theorem uniform : ∀ entry ∈ ordinary,
    RV.decode entry.bits = some ((hashPreparation (.blakeRound 0)).rvInstruction 12) := by
  intro entry member
  rw [List.mem_singleton.mp member]
  kernel_rfl

theorem workers_eq : data.workers = workersFrom m0 9 := rfl

/-- The preparation of x12, final at cut 8. -/
theorem preparation : RVControlPreparation data ordinary 8 12 (hashPreparation (.blakeRound 0)) where
  program := .uniform uniform
  prefixScope := by
    rw [workers_eq, Delegation.MemoryData.windowRows, List.filter_eq_nil_iff]
    intro row member
    obtain ⟨k, small, rfl⟩ := row_mem_from member
    rw [write_time_from start k (by omega)]
    simp only [decide_eq_true_eq]
    omega
  afterInitial := by decide +kernel
  beforeTerminal := by decide +kernel

/-- The whole span writes in `(8, 48]`. -/
theorem window : data.workers.windowRows 8 48 = data.workers.rows := window_from start (by omega) (by omega)

theorem rows_length : data.workers.rows.length = 10 := calls_from

theorem rows_ne : data.workers.rows ≠ [] := List.ne_nil_of_length_pos (by rw [rows_length]; omega)

theorem window_ne : data.workers.windowRows 8 48 ≠ [] := by
  rw [window]
  exact rows_ne

theorem terminal_time : (timeOfPair data.machine.terminal.timestamp).value = 48 := by decide +kernel

theorem round_inputs : RVPreparedRoundInputs data before (callerPCs 4 10) [0] keys ordinary 0 8 where
  publicProgram := request_inputs
  ordinaryProgram := ordinary_image
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  family := family_from
  preparation := preparation
  prefixEmpty := prefix_from start (by omega)
  roundsBound := by rw [rows_length]
  duration := by rw [terminal_time, rows_length]

theorem window_inputs : RVPreparedRoundWindowInputs data before (callerPCs 4 10) [0] keys ordinary 0 8 48 where
  toRVPreparedRoundInputs := round_inputs
  calls := by rw [window, rows_length]; rfl
  spanDuration := rfl
  beforeTerminal := by rw [terminal_time]

/-- The one controller region: flags 0, `(8, 48]`. -/
def region : RoundRegion := ⟨0, 8, 48⟩

theorem region_inputs : RVRoundRegionInputs data ordinary region where
  family row member := family_from row (by
    show row ∈ data.workers.rows
    rw [← window]
    exact member)
  preparation := preparation
  roundsBound := by
    show (data.workers.windowRows 8 48).length ≤ 10
    rw [window, rows_length]
  duration := by
    show 48 = 8 + 4 * (data.workers.windowRows 8 48).length
    rw [window, rows_length]
  aligned := ⟨rfl, rfl⟩
  beforeTerminal := by
    show 48 ≤ _
    rw [terminal_time]

theorem protocol_inputs : RVPreparedProtocolInputs data before (callerPCs 4 10) [0] keys ordinary [region] where
  publicProgram := request_inputs
  ordinaryProgram := ordinary_image
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  scopes r member := by
    rw [List.mem_singleton.mp member]
    exact region_inputs
  coverage row member _ := ⟨region, List.mem_singleton_self _, by
    show row ∈ data.workers.windowRows 8 48
    rw [window]
    exact member⟩

theorem region_ne : data.workers.windowRows region.lower region.upper ≠ [] := window_ne

theorem started : 0 < (timeOfPair data.machine.initial.timestamp).value := by decide +kernel

end Airbender.NonVacuous.RoundCallers.Prepared
