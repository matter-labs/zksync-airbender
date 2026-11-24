module
public import Tests.TraceExecution
public import Proven.Trace.Family.Timestamps
public import Human.Circuits.AddSub.RowInput
public import Human.Helpers.Core.CircuitOutput
public import Mathlib.Tactic.IntervalCases
public import Proven.KernelRfl
public import Proven.Defs.Helpers.Decoder.ExternalInput

@[expose] public section

namespace Tests.OracleTrace
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def readAssignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 21 => 8
  | 33 => 0x5678
  | 34 => 0x1234
  | _ => 0
def addAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 19 => 8
  | 21 => 12
  | 4 | 5 | 8 | 10 | 42 | 43 | 44 => 1
  | 7 => 2
  | 23 => 6
  | 27 => 5
  | 25 => 0x5678
  | 26 | 34 => 0x1234
  | 33 => 0x5679
  | _ => 0
def hintAssignment : Nat → ZMod babyBearModulus
  | 0 => 8
  | 2 | 19 | 27 => 12
  | 21 => 16
  | 4 | 10 | 42 | 43 | 44 => 1
  | 23 => 9
  | 35 => 13
  | _ => 0
def readRow : Row babyBearModulus := ⟨.addSub, readAssignment⟩
def addRow : Row babyBearModulus := ⟨.addSub, addAssignment⟩
def hintRow : Row babyBearModulus := ⟨.addSub, hintAssignment⟩

def regToken (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩
def cells := Tests.TraceExecution.cells
def seed : List (MemoryToken babyBearModulus) := ROMView.nativeBootImage cells
def trace : Data babyBearModulus where
  rows := [addRow, hintRow, readRow]
  rom := ROM.table cells seed
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 12 (16, 0)
  initialMemory := seed
  terminalMemory := [regToken 0 14 0 0, regToken 1 8 0x5678 0x1234,
    regToken 2 10 0x5679 0x1234] ++ seed.drop 3

private theorem native_constraints (row : Row babyBearModulus) (member : row ∈ trace.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Row.constraints, readRow, addRow, hintRow,
    AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, readAssignment, addAssignment, hintAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, readAssignment, addAssignment,
         hintAssignment, limbBase, ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, readAssignment, addAssignment,
         hintAssignment, timestampBase, ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])

private theorem accepted : Accepted trace := by
  refine ⟨native_constraints, ?_, ?_, ?_⟩
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · change [trace.initial, addRow.finish, hintRow.finish, readRow.finish].Perm
      [hintRow.finish, readRow.finish, addRow.finish, trace.initial]
    exact (List.reverse_perm [trace.initial, addRow.finish, hintRow.finish, readRow.finish]).symm.trans
      (List.Perm.swap _ _ _)
  · decide

private theorem ports : NonDeterminism.StreamPorts trace [0x12345678, 0xbeef] := by
  intro row member read
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases read
  · cases read
  · decide

theorem short_stream_rejected : ¬ NonDeterminism.StreamPorts trace [] := by
  intro supplied
  have read := supplied readRow (by simp [trace]) (by decide)
  cases read

theorem wrong_response_rejected : ¬ NonDeterminism.StreamPorts trace [0xbeef] := by
  intro supplied
  have read := supplied readRow (by simp [trace]) (by decide)
  have impossible : (0xbeef : BitVec 32) = 0x12345678 := Option.some.inj read
  contradiction

end Tests.OracleTrace
