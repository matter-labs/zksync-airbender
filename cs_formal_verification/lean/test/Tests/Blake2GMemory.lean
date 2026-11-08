module
public import Slop.Final.Circuits.Blake2G.Theorems
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Keccak.Permutation
public import Slop.Blake2G.CallGroups
public import Slop.Blake2G.PhysicalWords
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.ReverseFold
public import Mathlib.Tactic.IntervalCases
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.Blake2GMemory
noncomputable section
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 0 ∨ column = 5 ∨ column = 12 then 1
  else if column = 1 then 5
  else if column = 8 then 4
  else if column = 9 then 8
  else if column = 10 then 12
  else if column = 14 ∨ column = 31 ∨ column = 32 then 64
  else if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 2 then 1
  else 0

private abbrev table : Table (ZMod babyBearModulus) (fields 9) :=
  Blake2G.setupTable Blake2G.Control.controllerRows

private def indices : Vector Nat 19 :=
  #v[344640, 0, 0, 0, 0, 65536, 82240, 65600, 65536, 82240, 65600,
    0, 0, 0, 0, 65856, 82240, 65856, 82240]

private theorem indexBound (i : Fin 19) : indices[i] < 344896 := by
  fin_cases i <;> decide

private theorem tableQuery (i : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints table)).get
      ⟨i.val + 2, by rw [Blake2G.lookup_count]; omega⟩).Contains (Verification.environment row) := by
  let index : Fin 344896 := ⟨indices[i], indexBound i⟩
  fin_cases i
  all_goals refine ⟨index, ?_⟩
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals change j < 9 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraints table) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.lookup_count] using hi
    by_cases small : i < 2
    · interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals decide
    · have source := tableQuery ⟨i - 2, by omega⟩
      have position : i - 2 + 2 = i := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, row, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]
    all_goals decide

private def native : Delegation.Row babyBearModulus := ⟨.blakeG, row⟩
private def setup : Delegation.Setup babyBearModulus :=
  Delegation.modeledSetup (fun _ => Vector.replicate 6 0)
private def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd
private theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

private def boundaryRow (column : Nat) : ZMod babyBearModulus :=
  if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 0 then 1 else row column

private theorem boundaryTableQuery (i : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints table)).get
      ⟨i.val + 2, by rw [Blake2G.lookup_count]; omega⟩).Contains
        (Verification.environment boundaryRow) := by
  let index : Fin 344896 := ⟨indices[i], indexBound i⟩
  fin_cases i
  all_goals refine ⟨index, ?_⟩
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals change j < 9 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem boundaryCore : FlatOperation.ConstraintsHoldFlat (Verification.environment boundaryRow)
    (Blake2G.importedConstraints table) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.lookup_count] using hi
    by_cases small : i < 2
    · interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals decide
    · have source := boundaryTableQuery ⟨i - 2, by omega⟩
      have position : i - 2 + 2 = i := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

private theorem boundaryClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment boundaryRow)
    (Blake2G.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, boundaryRow, row, Trace.timestampBase,
      ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]
    all_goals decide

private def retimeSeed (token : MemoryToken babyBearModulus) : MemoryToken babyBearModulus :=
  { token with time := (1, 0) }

private def boundaryNative : Delegation.Row babyBearModulus := ⟨.blakeG, boundaryRow⟩
private def boundaryData : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [boundaryNative]
  initial := data.initial.map retimeSeed
  terminal := boundaryNative.memorySteps.map Prod.snd

private theorem boundaryAccepted : Delegation.MemoryAccepted boundaryData := by
  constructor
  · intro actual member
    simp only [boundaryData, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append boundaryCore boundaryClocks
  · have reads : boundaryData.steps.map Prod.fst = boundaryData.initial := by decide
    have writes : boundaryData.steps.map Prod.snd = boundaryData.terminal := by rfl
    rw [reads, writes]
    exact List.perm_append_comm

theorem complete_request_controls_repeat :
    Blake2G.controlAt false 160 = Blake2G.controlAt false 0 ∧
      Blake2G.controlAt true 112 = Blake2G.controlAt true 0 := by decide

end

end Tests.Blake2GMemory
