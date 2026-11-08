import Slop.Bigint.Claims

namespace Tests.BigintMemory
open Airbender Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 4 || column = 38 then 64
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if 216 ≤ column ∧ column < 273 ∧ (column - 216) % 3 = 2 then 1
  else 0

private def native : Delegation.Row babyBearModulus := ⟨.bigint, row⟩

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; decide)
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; decide)
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; decide)
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; decide)
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; decide)
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; decide)

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, row]
  all_goals decide

private def setup : Delegation.Setup babyBearModulus :=
  ⟨Bigint.setupTable, { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩

def cells : List Cell :=
  [.register 10] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194304 + 4 * i))) ++
    [.register 11] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194336 + 4 * i))) ++
    [.register 12]

def data : Delegation.MemoryData babyBearModulus where
  setup := setup
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

end Tests.BigintMemory
