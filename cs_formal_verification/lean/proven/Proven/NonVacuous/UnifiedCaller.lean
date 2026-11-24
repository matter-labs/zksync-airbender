module
public import Proven.NonVacuous.BigintPool
public import Proven.NonVacuous.UnifiedBoot
public import Human.Helpers.UnifiedReduced.RVMixedMemory
public import Human.Helpers.Delegation.NativeWindows

@[expose] public section

/-! A unified caller trace: one unified row issuing a bigint delegation (`csrrw x0, 0x7CA, x0`, ROM bytes
    `73 10 A0 7C` at PC 0) at clock four, and the bigint worker of `Proven/NonVacuous/BigintPool.lean` fulfilling it at
    invocation clock five; one architectural memory permutation over x0 and the worker's cells. The witness that
    the assumptions of the unified caller claims can be met (`Human/Trace/UnifiedReduced/RVCallerTheorems.lean`). -/

namespace Airbender.NonVacuous.UnifiedCaller
open Trace Arithmetic List Verification UnifiedReduced.Caller

/-- The caller row: clock 4, rs1 = rd = x0, rs2 = the bigint CSR 0x7CA (column 6, and 38 for the virtual port's
    address), selector seven (column 18); the destination port reads x0 as the source port left it (clock 4,
    column 46); 123-125 are the clock-comparison borrows. -/
def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 30 ∨ v = 46 then 4
  else if v = 32 then 8
  else if v = 4 ∨ v = 18 ∨ v = 123 ∨ v = 124 ∨ v = 125 then 1
  else if v = 6 ∨ v = 38 then 0x7CA
  else 0

def row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩

/-- The starting state of the bigint pool with the caller instruction at ROM address 0. -/
def before : RV.State :=
  { Bigint.before with rom := fun a => if a = 0 then 0x73 else if a = 1 then 0x10 else if a = 2 then 0xA0
      else if a = 3 then 0x7C else 0 }

noncomputable def setupChecked : CheckedTable (ZMod babyBearModulus) :=
  staticChecked (UnifiedReduced.Setup.tableRV before) rfl

noncomputable def checkedTables : List (CheckedTable (ZMod babyBearModulus)) :=
  List.replicate 13 range16Checked ++ List.replicate 5 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.tableRV (p := babyBearModulus)
      before))).map Lookup.table = checkedTables.map CheckedTable.table := by
  rfl

theorem satisfies : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV before)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl))
    (holds_of_checkOps UnifiedBoot.timestamp_tables (by kernel_rfl))

def program : List Delegation.Caller.RVProgramEntry := [⟨0, 0x7CA01073#32, ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩]

theorem program_image : Delegation.Caller.rvProgramImage before [0] = some program := by kernel_rfl

/-- The bigint worker pool, with the unified machine's modeled tables. -/
noncomputable def workers : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := [Bigint.native]
  initial := Bigint.native.memorySteps.map Prod.fst
  terminal := Bigint.native.memorySteps.map Prod.snd

def cells : List Cell := .register 0 :: Bigint.cells

/-- x0 as the caller's destination port leaves it. -/
def x0Final : MemoryToken babyBearModulus :=
  writeToken row.columns assignment UnifiedReduced.importedConstraintsMemoryPorts[2]

noncomputable def machine : UnifiedTrace babyBearModulus where
  rows := [row]
  rom := UnifiedReduced.Setup.tableRV before
  initial := row.start
  terminal := row.finish
  initialMemory := (Cell.register 0).initialToken 0 :: Bigint.native.memorySteps.map Prod.fst
  terminalMemory := x0Final :: Bigint.native.memorySteps.map Prod.snd

noncomputable def data : RVRequestTrace babyBearModulus := ⟨machine, workers, program⟩

theorem callers : data.callers = [row] := by
  simp only [RVRequestTrace.callers, data, machine]
  rw [List.filter_cons_of_pos (by decide +kernel), List.filter_nil]

theorem checks : RVRequestChecks data where
  constraints current member := by
    simp only [data, machine, List.mem_singleton] at member
    subst current
    exact satisfies
  active current member := by
    simp only [data, machine, List.mem_singleton] at member
    subst current
    rfl
  states := List.Perm.swap _ _ []
  decoded current member := by
    rw [callers, List.mem_singleton] at member
    subst current
    exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩
  workerConstraints current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    exact holds_append Bigint.core Bigint.clocks
  workerActive current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    rfl
  requests := by
    rw [Delegation.Requests.Matching, RVRequestTrace.calls, callers]
    decide +kernel

theorem accepted : RVMixedMemoryAccepted data [] where
  toRVRequestChecks := checks
  ordinaryDecoded current member notCaller := by
    rw [callers] at notCaller
    simp only [data, machine, List.mem_singleton] at member notCaller
    exact absurd member notCaller
  memory := by
    rw [RVRequestTrace.mixedSteps]
    decide +kernel

theorem request_inputs : RVRequestInputs data before [0] where
  image := program_image
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem inputs : RVMixedMemoryInputs data [] before [0] [] cells where
  publicProgram := request_inputs
  ordinaryProgram := rfl
  initialization := by kernel_rfl
  distinct := by decide +kernel
  aligned := by decide +kernel
  setup := rfl
  tables := rfl
  rounds current member family := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    cases family

theorem callers_ne : data.callers ≠ [] := by rw [callers]; exact List.cons_ne_nil _ _

/-- The worker writes at clock seven, inside the window `(4, 8]`. -/
theorem window_rows : data.workers.windowRows 4 8 = [Bigint.native] := by
  simp only [data, workers, Delegation.MemoryData.windowRows]
  rw [List.filter_cons_of_pos (by decide +kernel), List.filter_nil]

theorem window_ne : data.workers.windowRows 4 8 ≠ [] := by rw [window_rows]; exact List.cons_ne_nil _ _

end Airbender.NonVacuous.UnifiedCaller
