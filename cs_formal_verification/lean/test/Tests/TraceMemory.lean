module
public import Slop.Trace.ROMView
public import Slop.AddSub.Selectors
public import Slop.Trace.Pooled
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Core.BabyBearPrime
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.SubwordMemory.Output
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.RowHistory
public import Slop.Trace.Family.Timestamps

@[expose] public section

namespace Tests.TraceMemory
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- ADD x2,x1,x0 with x1 initially five. Clean's zero-initial memory must receive
-- an explicit initialization write before this nonzero operand can be read.
def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 19 then 4
  else if v = 21 then 8
  else if v = 4 ∨ v = 5 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 7 then 2
  else if v = 25 ∨ v = 33 then 5
  else 0

def row : Trace.Row babyBearModulus := ⟨.addSub, assignment⟩

def token (register clock value : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (clock, 0), Nat.pair value 0⟩

def trace (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Data babyBearModulus where
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

-- The second instruction reads the value written by the first, twice, then
-- writes ten to x1. Rows are stored in reverse execution order.
def secondAssignment (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 35 then 4
  else if v = 2 ∨ v = 19 ∨ v = 27 then 8
  else if v = 21 then 12
  else if v = 4 ∨ v = 7 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 5 ∨ v = 6 then 2
  else if v = 23 then 6
  else if v = 25 ∨ v = 29 ∨ v = 31 then 5
  else if v = 33 then 10
  else if v = 41 then 25 * 943718400 -- Shared Montgomery product intermediate.
  else 0

def secondRow : Trace.Row babyBearModulus := ⟨.addSub, secondAssignment⟩
def twoRows (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Data babyBearModulus :=
  { trace rom with
    rows := [secondRow, row]
    terminal := secondRow.finish
    terminalMemory := [token 0 5 0, token 1 10 10, token 2 9 5] }

theorem second_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment secondAssignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, secondAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, secondAssignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, secondAssignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem two_accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Accepted (twoRows rom) := by
  constructor
  · intro actual member
    simp only [twoRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact second_satisfies
    · exact local_satisfies
  · intro actual member
    simp only [twoRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · dsimp only [twoRows, trace]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · dsimp only [twoRows, trace]
    decide

theorem reordered_instruction_accesses (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ rows : List (Trace.Row babyBearModulus), rows.Perm (twoRows rom).rows ∧
      (∃ path, Trace.StatePath (twoRows rom) path ∧
        (path.zip path.tail).reverse = rows.map (fun row => (row.start, row.finish))) ∧
      ((rows.flatMap fun row => (Trace.rowEvents (twoRows rom).memoryEpoch row).reverse).map
        Prod.fst) = [(twoRows rom).memoryEpoch + 10, (twoRows rom).memoryEpoch + 9,
          (twoRows rom).memoryEpoch + 8, (twoRows rom).memoryEpoch + 6,
          (twoRows rom).memoryEpoch + 5, (twoRows rom).memoryEpoch + 4] := by
  let clocks : Trace.ClockBoundary (twoRows rom) :=
    ⟨(boundary rom).initial, (boundary rom).aligned, (boundary rom).memory⟩
  obtain ⟨rows, permutation, rowSorted, sorted, events⟩ := Trace.Proofs.native_row_order
    (by decide) (by decide) (two_accepted rom)
    clocks
  have statePath := Trace.Proofs.ordered_row_state_path (by decide) (by decide)
    (two_accepted rom) clocks permutation rowSorted
  have times := events.map Prod.fst
  have ordered : ((rows.flatMap fun row =>
      (Trace.rowEvents (twoRows rom).memoryEpoch row).reverse).map Prod.fst).Pairwise
        (fun a b => b < a) := List.pairwise_map.mpr sorted
  have expected : [(twoRows rom).memoryEpoch + 10, (twoRows rom).memoryEpoch + 9,
      (twoRows rom).memoryEpoch + 8, (twoRows rom).memoryEpoch + 6,
      (twoRows rom).memoryEpoch + 5, (twoRows rom).memoryEpoch + 4].Perm
      ((twoRows rom).nativeEvents.map Prod.fst) := by
    dsimp [twoRows, trace, Trace.Data.memoryEpoch, Trace.Data.nativeEvents, Trace.Data.memorySteps]
    decide
  exact ⟨rows, permutation, statePath, List.Perm.eq_of_pairwise' ordered (by simp)
    (times.trans expected.symm)⟩

def zeroTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "TraceValueFixture"
  length := 1
  row _ := Vector.replicate 9 0
  index _ := 0
  Spec entry := entry = Vector.replicate 9 0
  contains_iff _ := by simp
}

-- The nonzero public x1 value and its arithmetic result reach every actual
-- read and terminal cell. No read-value or per-read range premise is supplied.

def publicROM : Table (ZMod babyBearModulus) (fields 9) :=
  Trace.ROM.table [.register 0, .register 1, .register 2] (trace zeroTable).initialMemory

-- Equal combined address values are insufficient: the native pair encoding
-- rejects (65536, 0) as a representation of the canonical address (0, 1).
theorem noncanonical_ram_rejected :
    (Trace.MemoryAddress.mixed 10 false #v[25, 26]).code
      (fun v => if v = 10 then 1 else if v = 25 then (65536 : ZMod babyBearModulus) else 0) ≠
    (Trace.Cell.ram 65536).addressCode := by decide

end Tests.TraceMemory
