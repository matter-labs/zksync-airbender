module
public import Proven.KeccakSplit.ColumnParity.WitnessCheck
public import Proven.Constraints
public import Proven.KernelRfl
public import Proven.NonVacuous.Basic
public import Human.Trace.Workers.KeccakSplit.RVInputs
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A one-row split-Keccak pool initialized from an `RV.State`: the witness that the assumptions of the split
    workers' operation and write-range claims can be met. The row is the first call of the schedule, column parity
    x = 0 of round 0, on a zero state: x10 = 0 (control 0, written 8), x11 = 0x400000, the lanes in slots 0, 5, 10,
    15, 20 and C[0] (slot 25), RAM zero. Its imported constraints are checked by one kernel evaluation each
    (`Proven/WitnessCheck.lean`), the exported setup at the seven formula rows the queries use: iota bytes (rows 0,
    8192, 24576, 57344), slots (65537), control (65659) and the zero XOR5 row (65780). -/

namespace Airbender.NonVacuous.KeccakSplit
open Trace Keccak.Split.Native

/-- The row's assignment, by imported variable ID. -/
def row (v : Nat) : ZMod babyBearModulus :=
  if v = 0 then 1
  else if v = 1 then 5
  else if v = 5 then 8
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if v = 14 then 64
  else if 123 ≤ v ∧ v < 165 ∧ (v - 123) % 3 = 2 then 1
  else 0

def native : Keccak.Split.Native.Row babyBearModulus := ⟨.columnParity, row⟩

/-- The setup rows the row's queries use. -/
def setupRows : List Nat := [0, 8192, 24576, 57344, 65537, 65659, 65780]

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.Split.ColumnParity.importedConstraints Keccak.Split.ColumnParity.setup) :=
  Keccak.Split.ColumnParity.holds_of_check setupRows (by kernel_rfl)

theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.Split.ColumnParity.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Keccak.Split.ColumnParity.timestamps_of_check (by kernel_rfl)

/-- The row's ports, in native order: x10, x11, then the low and high word of slots 0, 5, 10, 15, 20 and 25. -/
def cells : List Cell :=
  [.register 10, .register 11, .ram 0x400000, .ram 0x400004, .ram 0x400028, .ram 0x40002C, .ram 0x400050,
    .ram 0x400054, .ram 0x400078, .ram 0x40007C, .ram 0x4000A0, .ram 0x4000A4, .ram 0x4000C8, .ram 0x4000CC]

/-- The starting state: control 0 in x10, the state pointer in x11, everything else zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 11 then 0x400000 else 0
  rom _ := 0
  mem _ := 0

def data : MemoryData babyBearModulus where
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : MemoryAccepted data := by
  constructor
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

theorem initialization :
    initialImageRV before cells = some (native.memorySteps.map Prod.fst : List (MemoryToken babyBearModulus)) := by
  kernel_rfl

theorem active : ∀ current ∈ data.rows, current.assignment current.columns.execute = 1 := by
  intro current member
  simp only [data, List.mem_singleton] at member
  subst current
  decide

theorem operation_inputs : RVOperationInputs data before cells where
  memory := {
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
  active := active

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide

theorem reads_bounded :
    native.memorySteps ≠ [] ∧ ∀ step ∈ native.memorySteps, step.1.word.Bounded := by
  decide +kernel

end Airbender.NonVacuous.KeccakSplit
