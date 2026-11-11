module
public import Slop.NonVacuous.HashCallers.UnifiedBlock
public import Slop.NonVacuous.HashCallers.Joint
public import Slop.NonVacuous.Blake2GSpan.Span
public import Slop.NonVacuous.Basic
public import Slop.WitnessCheck
public import Slop.KernelRfl
public import Human.Trace.UnifiedReduced.RVPreparedHashWindows
public import Human.Trace.UnifiedReduced.RVPreparedRoundWindows

@[expose] public section

/-! A prepared unified caller trace issuing a complete reduced G span: `addi x12, x0, 128` at PC 0 (clock 4, the
    preparation `hashPreparation (.blakeG true)`), then 56 callers `csrrw x0, 0x7C8, x0` at PC `4 + 4 k` and clock
    `8 + 4 k`, fulfilled by the span of `Span.lean` invoked at `9 + 4 k`, which reads x12 as the preparation wrote it.
    One joint memory permutation over x0 and the span's cells. The witness that the assumptions of the prepared
    G-span caller claims (`Human/Trace/UnifiedReduced/RVCallerTheorems.lean`) can be met, with the window `(8, 232]`.
    The one preparation row is checked by one kernel evaluation (`Slop/WitnessCheck.lean`); the callers and the
    span are generic (`UnifiedBlock.lean`, `Span.lean`). -/

namespace Airbender.NonVacuous.HashCallers.Prepared
open Trace NonVacuous.Blake2GSpan UnifiedReduced.Caller UnifiedBlock Verification

local notation "P" => babyBearModulus

/-- `addi x12, x0, 128` (`0x08000613`, bytes `13 06 00 08`). -/
def prepBytes (a : Nat) : BitVec 8 := if a = 0 then 0x13 else if a = 1 then 0x06 else if a = 2 then 0x00 else 0x08

/-- The span's starting state with the preparation at ROM address 0 and the callers after it. -/
def before : RV.State := { Blake2GSpan.before with rom := rom 4 prepBytes }

/-- The preparation row at PC 0 and clock 4: rd = x12 (columns 7, 44), immediate 128 (8) and result 128 (50), the
    ADD selector (11); the second port reads x0 as the first left it (clock 4, column 40); the destination port reads
    x12's seed 128 (48). -/
def prepColumn (v : Nat) : Nat :=
  if v = 2 then 4 else if v = 30 then 4 else if v = 40 then 4 else if v = 32 then 8
  else if v = 4 then 1 else if v = 11 then 1 else if v = 123 then 1 else if v = 124 then 1 else if v = 125 then 1
  else if v = 7 then 12 else if v = 44 then 12 else if v = 8 then 128 else if v = 50 then 128 else if v = 48 then 128
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

/-- x12 as the preparation leaves it: 128, written at clock 6. -/
def x12Token : MemoryToken P :=
  writeToken UnifiedReduced.importedConstraintsTraceColumns prepAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]

/-- The preparation's steps: x0 refreshed at clocks 4 and 5, x12 written. -/
def prepSteps : List (Cell × MemoryToken P) := [(.register 0, x0Token 4), (.register 0, x0Token 5), (.register 12, x12Token)]

theorem prep_edges : (machinePorts prep).toList.map (fun port =>
    (readToken prep.assignment port, writeToken prep.columns prep.assignment port)) = runEdges seed prepSteps := by
  decide +kernel

/-- The span's start: the seed with x12 as prepared. -/
def m0 : Memory := Function.update seed (.register 12) x12Token

theorem start : Start m0 9 :=
  ⟨inv_control (inv_mono seed_inv (by omega)) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel), rfl, by decide⟩

theorem room : Room 4 8 5 56 := ⟨by omega, by decide, by omega⟩

def machineSteps : List (Cell × MemoryToken P) := prepSteps ++ (List.range 56).flatMap fun k => x0Steps (8 + 4 * k)

noncomputable def workers : Delegation.MemoryData P := workersFrom m0 9

noncomputable def machine : UnifiedTrace P where
  rows := prep :: callerRows 4 8 5 56
  rom := UnifiedReduced.Setup.tableRV before
  initial := prep.start
  terminal := (callerRow 4 8 5 55).finish
  initialMemory := keys.map seed
  terminalMemory := keys.map (runFinal (runFinal seed machineSteps) (spanSteps m0 9))

/-- The ordinary program: the preparation. -/
def ordinary : List UnifiedReduced.RVProgramEntry := [⟨0, 0x08000613#32, ⟨.machine, 0, 0, 12, ⟨128, 0⟩, 1, 0⟩⟩]

noncomputable def data : RVRequestTrace P := ⟨machine, workers, program 4 56⟩

theorem callers : data.callers = callerRows 4 8 5 56 := by
  simp only [RVRequestTrace.callers, data, machine]
  rw [List.filter_cons_of_neg (by decide +kernel)]
  exact filter_selected

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by decide : 0 < 56)))

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
    have first : prep.finish = (callerRow 4 8 5 0).start := by kernel_rfl
    change (prep.start :: prep.finish :: (callerRows 4 8 5 56).map Row.finish).Perm
      ((callerRow 4 8 5 55).finish :: prep.start :: (callerRows 4 8 5 56).map Row.start)
    rw [first]
    exact ((states 55).cons _).trans (List.Perm.swap _ _ _)
  decoded row member := decoded room row (by rw [callers] at member; exact member)
  workerConstraints := (accepted_from start).constraints
  workerActive := execute_from
  requests := by
    rw [Delegation.Requests.Matching, RVRequestTrace.calls, RVRequestTrace.fulfillments, callers]
    change Delegation.Requests.Matching ((callerRows 4 8 5 56).map fun row => request row.assignment)
      ((workersFrom m0 (8 + 1)).rows.map Delegation.Requests.fulfillment)
    rw [requests, fulfillments]
    exact List.perm_append_comm

/-- The machine's edges are the run of its steps from the seed; the run leaves the span's cells as `m0`. -/
theorem machine_run :
    runEdges seed prepSteps ++ (List.range 56).flatMap (fun k => x0Edges (previousOf 5 8 k) (8 + 4 * k)) =
      runEdges seed machineSteps ∧ ∀ c ∈ cells, runFinal seed machineSteps c = m0 c := by
  have first : runFinal seed prepSteps (.register 0) = x0Token (previousOf 5 8 0) := by decide +kernel
  obtain ⟨run, untouched⟩ := x0_run (base := runFinal seed prepSteps) (clock := fun k => 8 + 4 * k) 56 first previous_chain
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
    change (keys.map seed ++ ((prep :: callerRows 4 8 5 56).flatMap _ ++ (workersFrom m0 9).steps).map Prod.snd).Perm
      (keys.map _ ++ ((prep :: callerRows 4 8 5 56).flatMap _ ++ (workersFrom m0 9).steps).map Prod.fst)
    rw [List.flatMap_cons, prep_edges, UnifiedBlock.edges]
    refine joint_matching run.symm (fun step member => ?_) agree start
    rcases List.mem_append.mp member with early | late
    · simp only [prepSteps, List.mem_cons, List.not_mem_nil, or_false] at early
      rcases early with rfl | rfl | rfl <;> decide +kernel
    · obtain ⟨k, -, present⟩ := List.mem_flatMap.mp late
      simp only [x0Steps, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact List.mem_cons_self ..

theorem readable : ∀ cell ∈ keys, (cell.readRV before).isSome := by decide +kernel

theorem initialization : initialImageRV before keys = some data.machine.initialMemory := initial_image readable

theorem request_inputs : RVRequestInputs data before (callerPCs 4 56) where
  image := program_image (prefixBytes := prepBytes) rfl rfl (by decide)
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem ordinary_image : rvProgramImageWith UnifiedReduced.rvDecoderFields before [0] = some ordinary := by kernel_rfl

/-- The preparation decodes to the G span's entry control literal. -/
theorem uniform : ∀ entry ∈ ordinary,
    RV.decode entry.bits = some ((hashPreparation (.blakeG true)).rvInstruction 12) := by
  intro entry member
  rw [List.mem_singleton.mp member]
  kernel_rfl

/-- The span writes after clock 8. -/
theorem prefix_scope : data.workers.windowRows 4 8 = [] := by
  change (workersFrom m0 9).windowRows 4 8 = []
  rw [Delegation.MemoryData.windowRows, List.filter_eq_nil_iff]
  intro row member
  obtain ⟨k, small, rfl⟩ := row_mem_from member
  rw [write_time_from start k (by omega)]
  simp only [decide_eq_true_eq]
  omega

/-- The preparation of x12, final at cut 8. -/
theorem preparation : RVControlPreparation data ordinary 8 12 (hashPreparation (.blakeG true)) where
  program := .uniform uniform
  prefixScope := prefix_scope
  afterInitial := by decide +kernel
  beforeTerminal := by decide +kernel

/-- The whole span writes in `(8, 232]`. -/
theorem window : data.workers.windowRows 8 232 = data.workers.rows := window_from start (by omega) (by omega)

theorem window_ne : data.workers.windowRows 8 232 ≠ [] := by
  rw [window]
  exact List.ne_nil_of_length_pos (by rw [show data.workers = workersFrom m0 9 from rfl, calls_from]; omega)

theorem window_family : ∀ row ∈ data.workers.windowRows 8 232, row.family = (Delegation.Caller.HashSpan.blakeG true).family := by
  rw [window]
  exact family_from

theorem window_calls : (data.workers.windowRows 8 232).length = (Delegation.Caller.HashSpan.blakeG true).callCount := by
  rw [window]
  exact calls_from

theorem before_terminal : 232 ≤ (timeOfPair data.machine.terminal.timestamp).value := by decide +kernel

theorem hash_window_inputs :
    RVPreparedHashWindowInputs data before (callerPCs 4 56) [0] keys ordinary (.blakeG true) 8 232 where
  publicProgram := request_inputs
  ordinaryProgram := ordinary_image
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  family := window_family
  roundsAbsent row member := by rw [family_from row member]; decide
  profile := by decide
  preparation := preparation
  calls := window_calls
  duration := rfl
  beforeTerminal := before_terminal

/-- The one prepared G window. -/
def hashWindow : HashWindow := ⟨.blakeG true, 8, 232⟩

theorem ordered : WindowsOrdered hashWindow.lower ([hashWindow].map HashWindow.interval) :=
  ⟨le_rfl, by decide, rfl, rfl, trivial⟩

theorem protocol_inputs : RVPreparedProtocolInputs data before (callerPCs 4 56) [0] keys ordinary [] where
  publicProgram := request_inputs
  ordinaryProgram := ordinary_image
  initialization := initialization
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  scopes _ member := absurd member List.not_mem_nil
  coverage row member family := absurd family (by rw [family_from row member]; decide)

theorem protocol_window_inputs : ∀ window ∈ [hashWindow], RVPreparedProtocolWindowInputs data ordinary window := by
  intro window member
  rw [List.mem_singleton.mp member]
  exact ⟨window_family, preparation, window_calls, rfl, before_terminal⟩

theorem sequential : RVSequentialProgram ordinary := by
  intro entry member instruction decoded
  rw [uniform entry member] at decoded
  cases decoded
  exact .arithmetic (.addi _ _ _)

/-- The window `(8, 232]` holds the callers' entries (PC `4 + 4 k`) and not the preparation (PC 0). -/
theorem caller_region : RVProgramCallerRegion data ordinary .blakeG 8 232 := by
  refine ⟨fun entry member => ?_, fun entry member _ => ?_⟩
  · rw [List.mem_singleton.mp member]
    decide +kernel
  · obtain ⟨pc, -, rfl⟩ := List.mem_map.mp member
    rfl

theorem program_window_inputs : ∀ window ∈ [hashWindow], RVProgramProtocolWindowInputs data ordinary window := by
  intro window member
  rw [List.mem_singleton.mp member]
  exact ⟨caller_region, preparation, rfl, before_terminal⟩

end Airbender.NonVacuous.HashCallers.Prepared
