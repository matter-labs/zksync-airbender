module
public import Slop.Blake2Round.WitnessCheck
public import Slop.Constraints
public import Slop.KernelRfl
public import Slop.NonVacuous.Basic
public import Human.Helpers.Delegation.RVOperations
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A one-row extended-control Blake2s round pool initialized from an `RV.State`: the witness that the assumptions
    of `Blake2Round.Native.RVOperationExecutionClaim` can be met. The row is round 1 (round mask bit 1, neither the
    first nor a final round, no control flags) on a zero state, extended state and message: x10 = 0x400000 (8 state
    and 16 extended words), x11 = 0x400080 (16 message words), x12 = 0x100000 (written 0x200000, the next round
    bit), RAM zero. Its imported constraints are checked by one kernel evaluation each (`Slop/WitnessCheck.lean`),
    the exported setup by its row formulas. -/

namespace Airbender.NonVacuous.Blake2Round
open Trace

/-- The row's assignment, by imported variable ID. -/
def row (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 143 then 1
  else if v = 1 then 5
  else if v = 4 ∨ v = 102 then 64
  else if v = 101 then 128
  else if v = 136 then 16
  else if v = 138 then 32
  else if 632 ≤ v ∧ v < 761 ∧ (v - 632) % 3 = 2 then 1
  else 0

def native : Delegation.Row babyBearModulus := ⟨.blakeRound, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2Round.importedConstraints Blake2Round.setupTable) :=
  Blake2Round.holds_of_check (by kernel_rfl)

theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2Round.importedConstraintsTimestampLookups (p := babyBearModulus)) :=
  Blake2Round.timestamps_of_check (by kernel_rfl)

/-- The row's ports, in native order: x10, the 24 state words at x10, x11, the 16 message words at x11, x12. -/
def cells : List Cell :=
  [.register 10] ++ (List.range 24).map (fun i => .ram (BitVec.ofNat 32 (4194304 + 4 * i))) ++
    [.register 11] ++ (List.range 16).map (fun i => .ram (BitVec.ofNat 32 (4194432 + 4 * i))) ++
    [.register 12]

/-- The starting state: the two pointers in x10 and x11, round bit 1 in x12, everything else zero. -/
def before : RV.State where
  pc := 0
  regFile i := if i = 10 then 0x400000 else if i = 11 then 0x400080 else if i = 12 then 0x100000 else 0
  rom _ := 0
  mem _ := 0

/-- Any controller table: the round row does not look it up. -/
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

theorem round_mask : Blake2Round.Memory.RoundMask row 1 := by
  unfold Blake2Round.Memory.RoundMask Blake2Round.Control.RoundMask
  decide

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
    intro current member _
    simp only [data, List.mem_singleton] at member
    subst current
    exact ⟨1, round_mask⟩
  keccakActive := by
    intro current member family
    simp only [data, List.mem_singleton] at member
    subst current
    cases family

theorem aligned : ∀ cell ∈ cells, cell.Aligned := by decide

end Airbender.NonVacuous.Blake2Round
