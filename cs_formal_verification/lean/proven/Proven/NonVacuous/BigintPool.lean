module
public import Proven.Bigint.WitnessCheck
public import Proven.Constraints
public import Proven.KernelRfl
public import Proven.NonVacuous.Basic
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A one-row bigint delegation pool initialized from an `RV.State`: the witness that the delegation-pool claims'
    assumptions can be met (`Human/Trace/Delegation/RVTheorems.lean`, `ZeroTimestamp.lean`, `WritesRangeChecked.lean`,
    `Workers/Bigint/RVTheorems.lean`). The row is an active bigint call with zero operands: x10 = 0x400000,
    x11 = 0x400020, x12 = 128 (the control word), RAM zero; its imported constraints are checked by one kernel
    evaluation each (`Proven/WitnessCheck.lean`). -/

namespace Airbender.NonVacuous.Bigint
open Trace Arithmetic

/-- The row's assignment, by imported variable ID. -/
def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 4 || column = 38 then 64
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if 216 ≤ column ∧ column < 273 ∧ (column - 216) % 3 = 2 then 1
  else 0

def native : Delegation.Row babyBearModulus := ⟨.bigint, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraints Bigint.setupTable) :=
  Bigint.holds_of_check (by kernel_rfl)

theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Bigint.timestamps_of_check (by kernel_rfl)

/-- The row's ports, in native order: x10, the eight words at x10, x11, the eight words at x11, x12. -/
def cells : List Cell :=
  [.register 10] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194304 + 4 * i))) ++
    [.register 11] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194336 + 4 * i))) ++
    [.register 12]

/-- The starting state: the pointers and the control word in x10..x12, everything else zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400020 else if i = 12 then 128 else 0
  rom _ := 0
  mem _ := 0

/-- Any controller table: the bigint row does not look it up. -/
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

theorem inputs : Delegation.RVMemoryInputs data before cells where
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
    decide

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide

theorem operation_inputs : Delegation.RVOperationInputs data before cells control where
  publicState := inputs
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

theorem rows_ne : data.rows ≠ [] := List.cons_ne_nil _ _

theorem reads_bounded :
    native.memorySteps ≠ [] ∧ ∀ step ∈ native.memorySteps, step.1.word.Bounded := by
  decide +kernel

end Airbender.NonVacuous.Bigint
