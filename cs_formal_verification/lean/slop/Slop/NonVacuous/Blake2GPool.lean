module
public import Slop.Blake2G.WitnessCheck
public import Slop.Constraints
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A one-row Blake2s G delegation pool initialized from an `RV.State`: the witness that the assumptions of
    `Blake2G.Native.RVOperationExecutionClaim` can be met. The row (from `test/Tests/Blake2GMemory.lean`) is an
    active G call on zero words: x10 = 0x400000 (the four state words at stride 16), x11 = 0x400040 (two message
    words), x12 the control (0, written 1), RAM zero; its imported constraints are checked by one kernel evaluation
    each (`Slop/WitnessCheck.lean`). -/

namespace Airbender.NonVacuous.Blake2G
open Trace

/-- The row's assignment, by imported variable ID. -/
def row (column : Nat) : ZMod babyBearModulus :=
  if column = 0 ∨ column = 5 ∨ column = 12 then 1
  else if column = 1 then 5
  else if column = 8 then 4
  else if column = 9 then 8
  else if column = 10 then 12
  else if column = 14 ∨ column = 31 ∨ column = 32 then 64
  else if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 2 then 1
  else 0

def native : Delegation.Row babyBearModulus := ⟨.blakeG, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) :=
  Blake2G.holds_of_check (by kernel_rfl)

theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Blake2G.timestamps_of_check (by kernel_rfl)

/-- The row's ports, in native order: x10, the four state words, x11, the two message words, x12. -/
def cells : List Cell :=
  [.register 10, .ram 0x400000, .ram 0x400010, .ram 0x400020, .ram 0x400030, .register 11, .ram 0x400040,
    .ram 0x400044, .register 12]

/-- The starting state: the two pointers in x10 and x11, everything else zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400040 else 0
  rom _ := 0
  mem _ := 0

/-- Any controller table: the G row does not look it up. -/
def control : Fin 4096 → Vector Nat 6 := fun _ => #v[0, 0, 0, 0, 0, 0]

noncomputable def data : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup control
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

theorem operation_inputs : Delegation.RVOperationInputs data before cells control where
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
    intro current member family
    simp only [data, List.mem_singleton] at member
    subst current
    cases family

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide

end Airbender.NonVacuous.Blake2G
