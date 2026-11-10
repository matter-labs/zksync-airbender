module
public import Slop.NonVacuous.BigintPool
public import Slop.WitnessCheck
public import Human.Helpers.Delegation.RVRequestEffects
public import Human.Helpers.Delegation.RVMixedMemory
public import Human.Helpers.Delegation.RequestWindows

@[expose] public section

/-! A delegation caller and its worker: the witness that the assumptions of the caller claims can be met
    (`Human/Circuits/AddSub/RVCallerTheorems.lean`, `Human/Trace/Delegation/RVCallerTheorems.lean`).

    The program is `csrrw x0, 0x7CA, x0` (the bigint delegation, `0x7CA01073`, ROM bytes `73 10 A0 7C`) at PC 0.
    One selected ADD/SUB caller row executes it at clock four and issues the request `(0x7CA, 5)`; the one-row bigint
    pool of `Slop/NonVacuous/BigintPool.lean` (invocation clock five, x10..x12 = 0x400000, 0x400020, 128, RAM zero)
    fulfills it. Both rows' imported constraints are checked by one kernel evaluation each (`Slop/WitnessCheck.lean`). -/

namespace Airbender.NonVacuous.Caller
open Trace Arithmetic Verification Delegation Caller
open scoped List

/-- The caller row at PC 0 and clock 4 (the row of `Tests.DelegationOperationEffects`). Columns: 0-1 PC, 2-3 clock,
    4 execute, 6 the rs2 field (the virtual CSR `0x7CA`), 17 the delegation selector, 19-22 the next PC and clock,
    35 the x0 write's previous clock (the x0 read at 4), 42-44 the clock-comparison borrows. -/
def assignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 ∨ column = 35 then 4
  else if column = 21 then 8
  else if column = 4 ∨ column = 17 ∨ column = 42 ∨ column = 43 ∨ column = 44 then 1
  else if column = 6 then 0x7CA
  else 0

def row : Row babyBearModulus PooledFamily := ⟨.addSub, assignment⟩

theorem lookup_tables :
    (FlatOperation.lookups (AddSub.importedConstraints (p := babyBearModulus))).map Lookup.table =
      (List.replicate 6 range16Checked).map CheckedTable.table := by
  rfl

theorem timestamp_tables :
    (FlatOperation.lookups (AddSub.importedConstraintsTimestampLookups (p := babyBearModulus))).map Lookup.table =
      (List.replicate 8 timestampChecked).map CheckedTable.table := by
  rfl

theorem core : FlatOperation.ConstraintsHoldFlat (environment assignment) AddSub.importedConstraints :=
  holds_of_checkOps lookup_tables (by kernel_rfl)

theorem satisfies : FlatOperation.ConstraintsHoldFlat (environment assignment) AddSub.clockConstraints :=
  holds_append core (holds_of_checkOps timestamp_tables (by kernel_rfl))

theorem selected : Requests.Selected assignment := by decide +kernel

/-- The starting state: the delegation call at ROM address 0, the bigint pool's registers and zero RAM. -/
def before : RV.State where
  pc := 0
  regFile := Bigint.before.regFile
  rom a := if a = 0 then 0x73 else if a = 1 then 0x10 else if a = 2 then 0xA0 else if a = 3 then 0x7C else 0
  mem _ := 0

theorem decode : RV.decode (RV.read before.rom 0 4) = some (.delegate .bigint) := by kernel_rfl

def entry : Caller.RVProgramEntry := ⟨0, 0x7CA01073#32, ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩

def program : List Caller.RVProgramEntry := [entry]

theorem image : rvProgramImage before [0] = some program := by kernel_rfl

theorem query : (Caller.rvDecoderTable (p := babyBearModulus) program).Contains #[] (nativeQuery assignment) :=
  ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

/-- The bigint pool of `BigintPool`, with the modeled operation tables. -/
noncomputable def workers : MemoryData babyBearModulus where
  setup := modeledSetup Keccak.Controller.rows
  rows := [Bigint.native]
  initial := Bigint.native.memorySteps.map Prod.fst
  terminal := Bigint.native.memorySteps.map Prod.snd

/-- Every machine and worker cell: x0 (the caller's ports) and the worker's. -/
def cells : List Cell := .register 0 :: Bigint.cells

def seed : MemoryToken babyBearModulus := (Cell.register 0).initialToken 0

/-- The caller's x0 write. -/
def final : MemoryToken babyBearModulus := destinationToken assignment

noncomputable def machine : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV before cells), Verification.subwordTable (ROM.wordsRV before)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := seed :: workers.initial
  terminalMemory := final :: workers.terminal

noncomputable def data : RVRequestTrace babyBearModulus := ⟨machine, workers, program⟩

theorem callers : data.callers = [row] := by kernel_rfl

theorem callers_ne : data.callers ≠ [] := by
  rw [callers]
  exact List.cons_ne_nil _ _

theorem fulfillment : Requests.fulfillment Bigint.native = Requests.caller assignment := by decide +kernel

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
    exact query
  workerConstraints current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    exact holds_append Bigint.core Bigint.clocks
  workerActive current member := by
    simp only [data, workers, List.mem_singleton] at member
    subst current
    rfl
  requests := by
    change Requests.Matching (data.callers.map fun row => Requests.caller row.assignment)
      [Requests.fulfillment Bigint.native]
    rw [callers, fulfillment]
    exact List.perm_append_comm

theorem accepted : RVRequestAccepted data where
  toRVRequestChecks := checks
  workerMemory := List.perm_append_comm

theorem inputs : RVRequestInputs data before [0] where
  image := image
  initialClock := by decide +kernel
  initialAligned := by decide +kernel

theorem worker_initialization :
    initialImageRV before Bigint.cells = some (Bigint.native.memorySteps.map Prod.fst :
      List (MemoryToken babyBearModulus)) := by
  kernel_rfl

theorem memory_inputs : RVRequestMemoryInputs data before [0] Bigint.cells where
  publicProgram := inputs
  initialization := worker_initialization
  distinct := by decide
  aligned := Bigint.aligned

theorem rounds : ∀ current ∈ data.workers.rows, current.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask current.assignment round := by
  intro current member family
  simp only [data, workers, List.mem_singleton] at member
  subst current
  cases family

theorem operation_inputs : RVRequestOperationInputs data before [0] Bigint.cells where
  publicState := memory_inputs
  tables := rfl
  rounds := rounds

/-- The x0 chain of the caller: seed, its read, its write. -/
theorem register_perm :
    ([seed] ++ (architecturalSteps assignment).map Prod.snd).Perm
      ([final] ++ (architecturalSteps assignment).map Prod.fst) := by
  decide +kernel

/-- Caller x0 tokens and worker tokens, matched separately. -/
theorem shared_perm {α : Type} {a b : α} {S F W0 W1 : List α} (x0 : ([a] ++ S).Perm ([b] ++ F)) :
    ((a :: W0) ++ (S ++ W1)).Perm ((b :: W1) ++ (F ++ W0)) := by
  have left : ((a :: W0) ++ (S ++ W1)).Perm (([a] ++ S) ++ (W0 ++ W1)) := by
    simp only [List.cons_append, List.nil_append, List.perm_cons]
    calc W0 ++ (S ++ W1)
        _ = (W0 ++ S) ++ W1 := (List.append_assoc ..).symm
        _ ~ (S ++ W0) ++ W1 := List.perm_append_comm.append_right _
        _ = S ++ (W0 ++ W1) := List.append_assoc ..
  have right : ((b :: W1) ++ (F ++ W0)).Perm (([b] ++ F) ++ (W0 ++ W1)) := by
    simp only [List.cons_append, List.nil_append, List.perm_cons]
    calc W1 ++ (F ++ W0)
        _ = (W1 ++ F) ++ W0 := (List.append_assoc ..).symm
        _ ~ (F ++ W1) ++ W0 := List.perm_append_comm.append_right _
        _ = F ++ (W1 ++ W0) := List.append_assoc ..
        _ ~ F ++ (W0 ++ W1) := List.perm_append_comm.append_left _
  exact left.trans ((x0.append_right _).trans right.symm)

theorem shared_steps : data.sharedSteps = architecturalSteps assignment ++ Bigint.native.memorySteps := by
  simp only [RVRequestTrace.sharedSteps, data, machine, workers, MemoryData.steps, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  rfl

theorem shared_accepted : RVSharedMemoryAccepted data where
  toRVRequestChecks := checks
  callerRows := callers
  memory := by
    rw [shared_steps, List.map_append, List.map_append]
    exact shared_perm register_perm

theorem initialization : initialImageRV before cells = some data.machine.initialMemory := by kernel_rfl

theorem shared_inputs : RVSharedMemoryInputs data before [0] cells where
  publicProgram := inputs
  initialization := initialization
  distinct := by decide
  aligned := by decide

theorem shared_operation_inputs : RVSharedOperationInputs data before [0] cells where
  toRVSharedMemoryInputs := shared_inputs
  tables := rfl
  rounds := rounds

theorem window : windowCallers data.callers 4 8 ≠ [] := by
  rw [callers]
  decide +kernel

end Airbender.NonVacuous.Caller
