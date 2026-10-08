import Airbender.Review.Trace.Theorems

namespace Tests.TraceMemory
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- ADD x2,x1,x0 with x1 initially five. Clean's zero-initial memory must receive
-- an explicit initialization write before this nonzero operand can be read.
private def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 19 then 4
  else if v = 21 then 8
  else if v = 4 ∨ v = 5 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 7 then 2
  else if v = 25 ∨ v = 33 then 5
  else 0

private def row : Trace.Row babyBearModulus := ⟨.addSub, assignment⟩

private def token (register clock value : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (clock, 0), Nat.pair value 0⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := [token 0 0 0, token 1 0 5, token 2 0 0]
  terminalMemory := [token 0 5 0, token 1 4 5, token 2 6 5]

theorem local_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.ClockBoundary (trace rom) := by
  dsimp only [trace]
  constructor
  · change 4 < Trace.timestampBase ∧ 0 < Trace.timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem nonzero_clean_histories (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∀ source ∈ (trace rom).initialMemory, ∃ history, Trace.CellHistory (trace rom) source history := by
  apply Trace.cell_histories (accepted rom) (boundary rom)
  change ([token 0 0 0, token 1 0 5, token 2 0 0].map Trace.MemoryToken.address).Nodup
  decide

private def zeroTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "TraceValueFixture"
  length := 1
  row _ := Vector.replicate 9 0
  index _ := 0
  Spec entry := entry = Vector.replicate 9 0
  contains_iff _ := by simp
}

private theorem value_boundary : Trace.ValueBoundary (trace zeroTable) := by
  constructor
  · intro actual member
    simp [trace] at member
    rcases member with rfl | rfl | rfl <;>
      norm_num [Trace.MemoryToken.word, token, Arithmetic.Word.Bounded, Arithmetic.limbBase]
  · intro entry member _
    obtain ⟨i, rfl⟩ := member
    exact ⟨rfl, rfl⟩
  · intro entry member
    obtain ⟨i, rfl⟩ := member
    simp [Arithmetic.limbBase]

-- The nonzero public x1 value and its arithmetic result reach every actual
-- read and terminal cell. No read-value or per-read range premise is supplied.
theorem bounded_native_values :
    (∀ actual ∈ (trace zeroTable).rows, ∀ port ∈ actual.ports,
      (Trace.readToken actual.assignment port).word.Bounded) ∧
    (∀ cell ∈ (trace zeroTable).terminalMemory, cell.word.Bounded) :=
  ⟨Trace.read_bounds (accepted zeroTable) (boundary zeroTable) value_boundary,
    Trace.terminal_bounds (accepted zeroTable) (boundary zeroTable) value_boundary⟩

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .PC (0 : BitVec 32) }

theorem native_pc_bounds :
    (∀ actual ∈ (trace zeroTable).rows, actual.start.word.Bounded ∧ actual.finish.word.Bounded) ∧
      (trace zeroTable).terminal.word.Bounded := by
  apply Trace.pc_bounds (accepted zeroTable) (before := before) (timestamp := (4, 0))
  have pcRead : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  rw [Trace.initialState, pcRead]
  rfl

end Tests.TraceMemory
