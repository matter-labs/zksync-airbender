module
public import Slop.Keccak.WitnessCheck
public import Slop.Constraints
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A one-row Keccak special5 delegation pool initialized from an `RV.State`: the witness that the assumptions of
    `Keccak.Native.RVOperationExecutionClaim` can be met. The row (after `test/Tests/DelegationMemory.lean`) is an
    active Theta call (control 3: mode 3, iteration 0, round 0) on zero lanes, with the lane indices the modeled
    controller selects for it (`Controller.rows 2051` = 0, 5, 10, 15, 20, 29): x10 = 3 (written 11),
    x11 = 0x400000, RAM zero. Its imported constraints are checked by one kernel evaluation each
    (`Slop/WitnessCheck.lean`). -/

namespace Airbender.NonVacuous.Keccak
open Trace

/-- The row's assignment, by imported variable ID. -/
def row (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 66 ∨ v = 70 then 1
  else if v = 1 then 5
  else if v = 3 then 3
  else if v = 5 then 11
  else if 7 ≤ v ∧ v < 12 then (5 * (v - 7) : Nat)
  else if v = 12 then 29
  else if v = 14 then 64
  else if v = 86 then 8192 else if v = 87 then 24640
  else if v = 88 then 41088 else if v = 89 then 57536
  else if 222 ≤ v ∧ v < 264 ∧ (v - 222) % 3 = 2 then 1
  else 0

def native : Delegation.Row babyBearModulus := ⟨.keccak, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraints (Keccak.setupTable Keccak.Controller.rows)) :=
  Keccak.holds_of_check (by kernel_rfl)

theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Keccak.timestamps_of_check (by kernel_rfl)

/-- The row's ports, in native order: x10, x11, then the low and high word of lanes 0, 5, 10, 15, 20 and 29. -/
def cells : List Cell :=
  [.register 10, .register 11, .ram 0x400000, .ram 0x400004, .ram 0x400028, .ram 0x40002C, .ram 0x400050,
    .ram 0x400054, .ram 0x400078, .ram 0x40007C, .ram 0x4000A0, .ram 0x4000A4, .ram 0x4000E8, .ram 0x4000EC]

/-- The starting state: the control word in x10, the state pointer in x11, everything else zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 3 else if i = 11 then 0x400000 else 0
  rom _ := 0
  mem _ := 0

noncomputable def data : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

theorem initialization :
    initialImageRV before cells = some (native.memorySteps.map Prod.fst : List (MemoryToken babyBearModulus)) := by
  kernel_rfl

theorem operation_inputs : Delegation.RVOperationInputs data before cells Keccak.Controller.rows where
  publicState := {
    initialization := initialization
    distinct := by decide
    clockRoom := by
      intro current member
      simp only [data, List.mem_singleton] at member
      subst current
      decide
    invocationHigh := by
      intro current member
      simp only [data, List.mem_singleton] at member
      subst current
      decide }
  tables := rfl
  rounds := by
    intro current member family
    simp only [data, List.mem_singleton] at member
    subst current
    cases family
  keccakActive := by
    intro current member _
    simp only [data, List.mem_singleton] at member
    subst current
    decide

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide

end Airbender.NonVacuous.Keccak
