import Tests.KeccakTheta
import Slop.Keccak.CallHistory
import Slop.Delegation.NativeSegments
import Mathlib.Data.List.OfFn
import Slop.Delegation.NativeViews
import Slop.Keccak.CallPorts

namespace Tests.DelegationMemory
noncomputable section
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 14 then 64
  else if 222 ≤ column ∧ column < 264 ∧ (column - 222) % 3 = 2 then 1
  else Tests.KeccakTheta.row column

private def native : Delegation.Row babyBearModulus := ⟨.keccak, row⟩

theorem native_invocation_convention :
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).lo % 4 = 1 ∧
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).lo + 2 < timestampBase := by
  decide

theorem native_write_convention :
    (timeOfPair (native.writeToken Keccak.importedConstraintsMemoryPorts[0]).time).value = 7 ∧
    (timeOfPair (native.writeToken Keccak.importedConstraintsMemoryPorts[0]).time).value % 4 = 3 := by
  decide

theorem oracle_debug_assert_rejects_invocation :
    (decodeTimestamp row Keccak.importedConstraintsDelegationColumns.invocation).value % 4 ≠ 3 := by
  decide

private theorem queries_unchanged (i : Fin 42) :
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment row)) =
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment Tests.KeccakTheta.row)) := by
  fin_cases i
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals first | change j < 1 at hj | change j < 8 at hj
  all_goals interval_cases j
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraints Tests.KeccakTheta.setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have old := Verification.lookup_of_holds Tests.KeccakTheta.satisfies ⟨i, hi⟩
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    have same := queries_unchanged ⟨i, bound⟩
    simp only [List.get_eq_getElem] at same old
    simp only [Lookup.Contains, Verification.environment] at old ⊢
    exact Eq.mp (congrArg (fun entry =>
      ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup))[i]).table.Contains
        #[] entry) same.symm) old

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Keccak.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 30 := by simpa only [Keccak.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, row, Tests.KeccakTheta.row,
      Trace.timestampBase, ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]
    all_goals decide

private def setup : Delegation.Setup babyBearModulus :=
  ⟨{ name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, Tests.KeccakTheta.setup⟩

def cells : List Cell :=
  [.register 10, .register 11, .ram 4194304, .ram 4194308, .ram 4194344, .ram 4194348, .ram 4194384, .ram 4194388,
    .ram 4194424, .ram 4194428, .ram 4194464, .ram 4194468, .ram 4194504, .ram 4194508]

def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

theorem native_window_keeps_all_ports :
    Delegation.Proofs.windowRows data 6 7 = [native] ∧
    Trace.Proofs.Transfer.windowSteps (Delegation.Proofs.transferData data) 6 7 = native.memorySteps := by
  constructor
  · rfl
  · rw [← Delegation.Proofs.native_window_steps]
    rfl

end

end Tests.DelegationMemory
