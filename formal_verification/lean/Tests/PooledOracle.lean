import Airbender.Proofs.Trace.PooledOracleConsumption
import Airbender.Proofs.BabyBear
import Tests.ShiftBinopTimestamp

namespace Tests.PooledOracle
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def readAssignment (second : Bool) : Nat → ZMod babyBearModulus
  | 0 => if second then 8 else 0
  | 2 => if second then 12 else 4
  | 19 => if second then 12 else 4
  | 21 => if second then 16 else 8
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 23 => if second then 9 else 0
  | 27 => if second then 12 else 4
  | 35 => if second then 10 else 0
  | 33 => if second then 0xbeef else 0x5678
  | 34 => if second then 0 else 0x1234
  | _ => 0

private def shiftAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 13 | 23 => 8
  | 15 => 12
  | 17 => 5
  | 29 => 0x5678
  | 30 => 0x1234
  | 33 => 6
  | i => if i = 14 then 0 else Tests.ShiftBinopTimestamp.assignment false i

private def readRow (second : Bool) : Row babyBearModulus PooledFamily :=
  ⟨.addSub, readAssignment second⟩
private def shiftRow : Row babyBearModulus PooledFamily := ⟨.shiftBinop, shiftAssignment⟩
private def token (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩

-- Read x1, XOR x1,x0,x0, then read x1 again. Physical row order is scrambled.
private def trace : PooledTrace babyBearModulus where
  rows := [shiftRow, readRow true, readRow false]
  rom := ⟨ROM.table [] [], Verification.subwordTable (fun _ => 0)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 12 (16, 0)
  initialMemory := [token 0 0 0 0, token 1 0 0 0]
  terminalMemory := [token 0 13 0 0, token 1 14 0xbeef 0]

private theorem read_constraints (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (readAssignment second)) AddSub.clockConstraints := by
  cases second <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, readAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, readAssignment,
         limbBase, ZMod.val_ofNat, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, readAssignment,
         timestampBase, ZMod.val_ofNat, babyBearModulus])

private theorem shift_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment shiftAssignment) ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := ShiftBinop.importedConstraints)
    (right := ShiftBinop.importedConstraintsTimestampLookups)
  · have core := Tests.ShiftBinop.satisfies
    simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, Vector.map, Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
      Verification.range16, Verification.shiftBinopLookup,
      show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
      show (8 : ZMod babyBearModulus) + 4 + -12 = 0 by decide] at core ⊢
    refine ⟨?_, ?_, core.2.2.2.2⟩
    · have bound := Verification.range16_contains
        (entry := Expression.const (8 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
    · have bound := Verification.range16_contains
        (entry := Expression.const (0 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
  · simp [ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment]
    all_goals decide

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact shift_constraints
    · exact read_constraints true
    · exact read_constraints false
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · change [trace.initial, shiftRow.finish, (readRow true).finish, (readRow false).finish].Perm
      [(readRow true).finish, (readRow false).finish, shiftRow.finish, trace.initial]
    exact (List.reverse_perm [trace.initial, shiftRow.finish, (readRow true).finish,
      (readRow false).finish]).symm.trans (List.Perm.swap _ _ _)
  · decide

private theorem clocks : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro seed member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      change 0 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide

private theorem ports : NonDeterminism.Pooled.StreamPorts trace [0x12345678, 0xbeef, 0xcafe] := by
  intro row member selected
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases selected
  · decide
  · decide

theorem mixed_native_consumption :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, [0x12345678, 0xbeef, 0xcafe] = NonDeterminism.Pooled.consumed rows ++ rest :=
  NonDeterminism.Pooled.Proofs.native_consumption (by decide) (by decide) accepted clocks ports

theorem chronological_response_order :
    NonDeterminism.Pooled.consumed [readRow true, shiftRow, readRow false] = [0x12345678, 0xbeef] ∧
      NonDeterminism.Pooled.readIndex trace (readRow false) = 0 ∧
      NonDeterminism.Pooled.readIndex trace (readRow true) = 1 ∧ NonDeterminism.Pooled.readCount trace = 2 := by
  decide

theorem wrong_stream_order_rejected : ¬ NonDeterminism.Pooled.StreamPorts trace [0xbeef, 0x12345678] := by
  intro supplied
  have mismatch := supplied (readRow false) (by simp [trace]) (by decide)
  have impossible : (0xbeef : BitVec 32) = 0x12345678 := Option.some.inj mismatch
  contradiction

theorem short_stream_rejected : ¬ NonDeterminism.Pooled.StreamPorts trace [0x12345678] := by
  intro supplied
  have missing := supplied (readRow true) (by simp [trace]) (by decide)
  cases missing

theorem foreign_selector_ignored (family : PooledFamily) (other : family ≠ .addSub) :
    NonDeterminism.Pooled.isRead (⟨family, fun _ => 1⟩ : Row babyBearModulus PooledFamily) = false := by
  cases family <;> simp_all [NonDeterminism.Pooled.isRead]

end Tests.PooledOracle
