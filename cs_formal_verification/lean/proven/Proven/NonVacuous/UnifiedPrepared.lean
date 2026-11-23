module
public import Proven.NonVacuous.UnifiedCaller
public import Human.Helpers.UnifiedReduced.RVControlPreparation
public import Human.Helpers.UnifiedReduced.RVWindows

@[expose] public section

/-! A unified caller trace with a control preparation: `LUI x10, 0x400` at PC 0 (clock 4) writes the bigint
    worker's pointer, then `csrrw x0, 0x7CA, x0` at PC 4 (clock 8) issues the call, fulfilled by the bigint worker
    at invocation clock nine. The witness that the assumptions of the control-preparation caller claim can be met
    (`Human/Trace/UnifiedReduced/RVCallerTheorems.lean`), with cut 8. -/

namespace Airbender.NonVacuous.UnifiedPrepared
open Trace Arithmetic List Verification UnifiedReduced.Caller

/-- `LUI x10, 0x400` at PC 0 and clock 4: rd = x10 (columns 7, 44), immediate high limb 0x40 (9) and result
    0x400000 (51), the ADD selector (11); the second port reads x0 as the first port left it (clock 4, column 40). -/
def prepAssignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 30 ∨ v = 40 then 4
  else if v = 32 then 8
  else if v = 4 ∨ v = 11 ∨ v = 123 ∨ v = 124 ∨ v = 125 then 1
  else if v = 7 ∨ v = 44 then 10
  else if v = 9 ∨ v = 51 then 64
  else 0

/-- The caller at PC 4 and clock 8: the source port reads x0 as the preparation left it (clock 5, column 34), the
    destination port as the source port left it (clock 8, column 46). -/
def callerAssignment (v : Nat) : ZMod babyBearModulus :=
  if v = 0 then 4
  else if v = 2 ∨ v = 30 ∨ v = 46 then 8
  else if v = 32 then 12
  else if v = 34 then 5
  else if v = 4 ∨ v = 18 ∨ v = 123 ∨ v = 124 ∨ v = 125 then 1
  else if v = 6 ∨ v = 38 then 0x7CA
  else 0

/-- The same `LUI x10, 0x400` again at PC 8 and clock 12, after the call: x0 as the caller left it (clock 10,
    column 34) and as its own first port left it (clock 12, column 40); x10 as the worker left it (clock 11, column 46,
    value 0x400000 in 48-49). -/
def againAssignment (v : Nat) : ZMod babyBearModulus :=
  if v = 0 then 8
  else if v = 2 ∨ v = 30 ∨ v = 40 then 12
  else if v = 32 then 16
  else if v = 34 then 10
  else if v = 46 then 11
  else if v = 4 ∨ v = 11 ∨ v = 123 ∨ v = 124 ∨ v = 125 then 1
  else if v = 7 ∨ v = 44 then 10
  else if v = 9 ∨ v = 49 ∨ v = 51 then 64
  else 0

def prep : Row babyBearModulus UnifiedFamily := ⟨.machine, prepAssignment⟩
def again : Row babyBearModulus UnifiedFamily := ⟨.machine, againAssignment⟩
def caller : Row babyBearModulus UnifiedFamily := ⟨.machine, callerAssignment⟩

/-- The bigint worker row invoked at clock nine, reading x10 as the preparation wrote it (clock 6, column 216). -/
def workerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 9 else if column = 216 then 6 else Bigint.row column

def worker : Delegation.Row babyBearModulus := ⟨.bigint, workerAssignment⟩

theorem worker_core : FlatOperation.ConstraintsHoldFlat (environment workerAssignment)
    (Bigint.importedConstraints Bigint.setupTable) :=
  Bigint.holds_of_check (by kernel_rfl)

theorem worker_clocks : FlatOperation.ConstraintsHoldFlat (environment workerAssignment)
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Bigint.timestamps_of_check (by kernel_rfl)

/-- The starting state: the three instructions in ROM, x10 = 0, x11 = 0x400020, x12 = 128, RAM zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 11 then 0x400020 else if i = 12 then 128 else 0
  rom a := if a = 0 then 0x37 else if a = 1 then 0x05 else if a = 2 then 0x40 else if a = 3 then 0x00
    else if a = 4 then 0x73 else if a = 5 then 0x10 else if a = 6 then 0xA0 else if a = 7 then 0x7C
    else if a = 8 then 0x37 else if a = 9 then 0x05 else if a = 10 then 0x40 else 0
  mem _ := 0

noncomputable def setupChecked : CheckedTable (ZMod babyBearModulus) :=
  staticChecked (UnifiedReduced.Setup.tableRV before) rfl

noncomputable def checkedTables : List (CheckedTable (ZMod babyBearModulus)) :=
  List.replicate 13 range16Checked ++ List.replicate 5 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.tableRV (p := babyBearModulus)
      before))).map Lookup.table = checkedTables.map CheckedTable.table := by
  rfl

theorem prep_satisfies : FlatOperation.ConstraintsHoldFlat (environment prepAssignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV before)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl))
    (holds_of_checkOps UnifiedBoot.timestamp_tables (by kernel_rfl))

theorem again_satisfies : FlatOperation.ConstraintsHoldFlat (environment againAssignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV before)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl))
    (holds_of_checkOps UnifiedBoot.timestamp_tables (by kernel_rfl))

theorem caller_satisfies : FlatOperation.ConstraintsHoldFlat (environment callerAssignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV before)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl))
    (holds_of_checkOps UnifiedBoot.timestamp_tables (by kernel_rfl))

/-- The ordinary program: the two preparations. -/
def program : List UnifiedReduced.RVProgramEntry :=
  [⟨0, 0x00400537#32, ⟨.machine, 0, 0, 10, ⟨0, 64⟩, 1, 0⟩⟩, ⟨8, 0x00400537#32, ⟨.machine, 0, 0, 10, ⟨0, 64⟩, 1, 0⟩⟩]

/-- The caller program: the bigint call at PC 4. -/
def callerProgram : List Delegation.Caller.RVProgramEntry :=
  [⟨4, 0x7CA01073#32, ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩]

theorem program_image : rvProgramImageWith UnifiedReduced.rvDecoderFields before [0, 8] = some program := by
  kernel_rfl

theorem caller_image : Delegation.Caller.rvProgramImage before [4] = some callerProgram := by kernel_rfl

noncomputable def workers : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := [worker]
  initial := worker.memorySteps.map Prod.fst
  terminal := worker.memorySteps.map Prod.snd

def cells : List Cell := .register 0 :: Bigint.cells

def x0Final : MemoryToken babyBearModulus :=
  writeToken again.columns againAssignment UnifiedReduced.importedConstraintsMemoryPorts[1]

def x10Final : MemoryToken babyBearModulus :=
  writeToken again.columns againAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]

noncomputable def machine : UnifiedTrace babyBearModulus where
  rows := [prep, caller, again]
  rom := UnifiedReduced.Setup.tableRV before
  initial := prep.start
  terminal := again.finish
  initialMemory := (Cell.register 0).initialToken 0 :: (Cell.register 10).initialToken 0 ::
    (worker.memorySteps.map Prod.fst).tail
  terminalMemory := x0Final :: x10Final :: (worker.memorySteps.map Prod.snd).tail

noncomputable def data : RVRequestTrace babyBearModulus := ⟨machine, workers, callerProgram⟩

theorem callers : data.callers = [caller] := by
  simp only [RVRequestTrace.callers, data, machine]
  rw [List.filter_cons_of_neg (by decide +kernel), List.filter_cons_of_pos (by decide +kernel),
    List.filter_cons_of_neg (by decide +kernel), List.filter_nil]

theorem checks : RVRequestChecks data where
  constraints current member := by
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact prep_satisfies
    · exact caller_satisfies
    · exact again_satisfies
  active current member := by
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  states := by
    change [prep.start, prep.finish, caller.finish, again.finish].Perm
      [again.finish, prep.start, caller.start, again.start]
    have first : prep.finish = caller.start := by kernel_rfl
    have second : caller.finish = again.start := by kernel_rfl
    rw [first, second]
    exact List.perm_append_comm (l₁ := [_, _, _]) (l₂ := [_])
  decoded current member := by
    rw [callers, List.mem_singleton] at member
    subst current
    exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩
  workerConstraints current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    exact holds_append worker_core worker_clocks
  workerActive current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    rfl
  requests := by
    rw [Delegation.Requests.Matching, RVRequestTrace.calls, callers]
    decide +kernel

theorem accepted : RVMixedMemoryAccepted data program where
  toRVRequestChecks := checks
  ordinaryDecoded current member notCaller := by
    rw [callers] at notCaller
    simp only [data, machine, List.mem_cons, List.not_mem_nil, or_false] at member notCaller
    rcases member with rfl | rfl | rfl
    · exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩
    · exact absurd rfl notCaller
    · exact ⟨⟨1, by decide +kernel⟩, by kernel_rfl⟩
  memory := by
    rw [RVRequestTrace.mixedSteps]
    decide +kernel

theorem request_inputs : RVRequestInputs data before [4] where
  image := caller_image
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem inputs : RVMixedMemoryInputs data program before [4] [0, 8] cells where
  publicProgram := request_inputs
  ordinaryProgram := program_image
  initialization := by kernel_rfl
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  rounds current member family := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    cases family

theorem window_rows : data.workers.windowRows 4 8 = [] := by
  simp only [data, workers, Delegation.MemoryData.windowRows]
  rw [List.filter_cons_of_neg (by decide +kernel), List.filter_nil]

theorem window_rows_after : data.workers.windowRows 12 16 = [] := by
  simp only [data, workers, Delegation.MemoryData.windowRows]
  rw [List.filter_cons_of_neg (by decide +kernel), List.filter_nil]

/-- The worker writes at clock eleven, inside the window `(8, 16]` between the two preparations. -/
theorem window_ne : data.workers.windowRows 8 16 ≠ [] := by
  simp only [data, workers, Delegation.MemoryData.windowRows]
  rw [List.filter_cons_of_pos (by decide +kernel), List.filter_nil]
  exact List.cons_ne_nil _ _

theorem uniform : ∀ entry ∈ program, RV.decode entry.bits = some ((ControlLiteral.lui 0x400).rvInstruction 10) := by
  intro entry member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> kernel_rfl

/-- The preparation of x10 with `LUI 0x400`, final at cut 8. -/
theorem preparation : RVControlPreparation data program 8 10 (.lui 0x400) where
  program := .uniform uniform
  prefixScope := window_rows
  afterInitial := by decide +kernel
  beforeTerminal := by decide +kernel

/-- The second preparation, final at cut 16. -/
theorem preparation_again : RVControlPreparation data program 16 10 (.lui 0x400) where
  program := .uniform uniform
  prefixScope := window_rows_after
  afterInitial := by decide +kernel
  beforeTerminal := by decide +kernel

theorem callers_ne : data.callers ≠ [] := by rw [callers]; exact List.cons_ne_nil _ _

/-- The worker writes at clock eleven, inside the call's window `(8, 12]`. -/
theorem call_window : data.workers.windowRows 8 12 = [worker] := by
  simp only [data, workers, Delegation.MemoryData.windowRows]
  rw [List.filter_cons_of_pos (by decide +kernel), List.filter_nil]

theorem call_window_ne : data.workers.windowRows 8 12 ≠ [] := by rw [call_window]; exact List.cons_ne_nil _ _

/-- Both preparations are sequential (LUI) instructions. -/
theorem sequential : RVSequentialProgram program := by
  intro entry member instruction decoded
  rw [uniform entry member] at decoded
  cases decoded
  exact .arithmetic (.lui _ _)

/-- The window `(8, 12]` holds the caller's entry (PC 4) and neither preparation (PC 0 and 8). -/
theorem caller_region : RVProgramCallerRegion data program .bigint 8 12 := by
  refine ⟨fun entry member => ?_, fun entry member _ => ?_⟩
  · simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · simp only [data, callerProgram, List.mem_singleton] at member
    subst entry
    rfl

end Airbender.NonVacuous.UnifiedPrepared
