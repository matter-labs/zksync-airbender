import Airbender.Review.UnifiedReduced.Theorems
import Airbender.Proofs.BabyBear

namespace Tests.UnifiedReduced
open Airbender Airbender.Arithmetic

-- A row using only the setup's disabled-query entry.
private def zeroSetup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private def row : Nat → ZMod babyBearModulus
  | 0 => 65534
  | 1 | 30 => 2
  | 4 | 11 | 128 | 129 | 130 => 1
  | 31 => 3
  | 32 => 4
  | _ => 0

set_option maxRecDepth 8192 in
private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (UnifiedReduced.importedConstraints zeroSetup) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)

example : (Word.mk (row 30).val (row 31).val).toBitVec = (Word.mk 65534 2).toBitVec + 4 := by
  have result := UnifiedReduced.Proofs.pc_successor (p := babyBearModulus)
    (initial := ⟨65534, 2⟩) (final := ⟨(row 30).val, (row 31).val⟩)
    (by decide) satisfies rfl ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩
  exact result.2.2

example : (∑ i : Fin 18, (row UnifiedReduced.Variables.dispatchColumns[i]).val) ≤ 1 :=
  UnifiedReduced.Proofs.dispatch_count (by decide) satisfies rfl


open Airbender.Reference.RiscV
open Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail

private def aliasedRow : Nat → ZMod babyBearModulus
  | 5 | 6 | 7 | 38 | 44 => 1
  | 36 | 42 => 123
  | 50 => 246
  | 80 => 123 * 123 * 943718400
  | i => row i

set_option maxRecDepth 8192 in
private theorem aliased_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment aliasedRow)
      (UnifiedReduced.importedConstraints zeroSetup) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, aliasedRow, row, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)

private def before : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (196606 : BitVec 32)) }

private def input : Input where
  row := ⟨.add, ⟨123, 0⟩, ⟨123, 0⟩, ⟨0, 0⟩, ⟨65534, 2⟩⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 1
  rd := .Regidx 1
  encodedImmediate := 0
  encodedUpperImmediate := 0
  before := before

private theorem contract : Contract input := by
  have read : run (SailRV32.Functions.rX_bits input.rs1) before = .ok (123 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  constructor
  · intro _
    exact ⟨123, read, fun _ => rfl⟩
  · intro _
    exact ⟨123, read, fun _ => rfl⟩
  · simp [input]
  · simp [input]
  · apply read_register
    simp [input, before, Word.toBitVec, Word.value, limbBase]

/-- A complete imported ADD row with both sources/destination aliased and a PC
    carry establishes the same full native Sail state, not just the result word. -/
example : spec input ⟨⟨246, 0⟩, ⟨2, 3⟩⟩ := by
  apply UnifiedReduced.babyBear_soundness zeroSetup input _ aliasedRow
  refine ⟨?_, aliased_satisfies, ?_⟩
  · constructor
    · constructor
      · rfl
      · rfl
      · rfl
    · intro _
      constructor <;> constructor <;> decide
    · decide
    · exact contract
  · constructor <;> rfl

example : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment (fun i => if i = 12 then 1 else aliasedRow i))
    (UnifiedReduced.importedConstraints zeroSetup) := by
  intro h
  have excluded := UnifiedReduced.Proofs.dispatch_exclusive (by decide) h rfl 0 rfl 1 (by decide)
  change (1 : ZMod babyBearModulus) = 0 at excluded
  exact one_ne_zero excluded

private def discarded : Input :=
  { input with
    row := ⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨65534, 2⟩⟩
    rd := zeroRegister
    encodedImmediate := 4095 }

private theorem discarded_contract : Contract discarded := by
  constructor
  · intro _
    refine ⟨123, ?_, ?_⟩
    · apply read_register
      simp [discarded, input, before, Std.ExtDHashMap.get?_insert]
    · simp [discarded]
  · simp [discarded]
  · simp [discarded]
  · simp [discarded]
  · apply read_register
    simp [discarded, input, before, Word.toBitVec, Word.value, limbBase]

/-- Original ADDI x0,x1,-1 still reads x1, while the circuit uses a zero-operand
    ADD row. No agreement or bound on the discarded original operand is assumed. -/
example : spec discarded ⟨⟨0, 0⟩, ⟨2, 3⟩⟩ := by
  apply UnifiedReduced.babyBear_soundness zeroSetup discarded _ row
  refine ⟨?_, satisfies, ?_⟩
  · constructor
    · constructor
      · rfl
      · rfl
      · simp [AddSub.Preprocessing, discarded]
    · simp [discarded]
    · decide
    · exact discarded_contract
  · constructor <;> rfl

private def triRow : Nat → ZMod babyBearModulus
  | 11 => 0
  | 20 | 52 | 53 | 54 | 55 => 1
  | 36 | 37 | 42 | 43 | 48 | 49 | 51 => 65535
  | 50 => 65533
  | 80 => 4294967295 * 4294967295 * 943718400
  | i => aliasedRow i

set_option maxRecDepth 8192 in
private theorem tri_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment triRow)
      (UnifiedReduced.importedConstraints zeroSetup) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, triRow, aliasedRow, row,
    Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (exact ⟨⟨0, by decide⟩, rfl⟩)

private def triBefore : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (4294967295 : BitVec 32) |>.insert .PC (196606 : BitVec 32)) }

private def triInput : UnifiedReduced.TriAdd.Input where
  left := ⟨65535, 65535⟩
  right := ⟨65535, 65535⟩
  oldDestination := ⟨65535, 65535⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 1
  rd := .Regidx 1
  pc := ⟨65534, 2⟩
  before := triBefore

private theorem tri_contract : UnifiedReduced.TriAdd.RegisterContract triInput := by
  have read : run (SailRV32.Functions.rX_bits triInput.rs1) triBefore =
      .ok (4294967295 : BitVec 32) triBefore := by
    apply read_register
    simp [triBefore, Std.ExtDHashMap.get?_insert]
  constructor
  · exact ⟨4294967295, read, fun _ => rfl⟩
  · exact ⟨4294967295, read, fun _ => rfl⟩
  · exact ⟨4294967295, read, fun _ => rfl⟩
  · apply read_register
    simp [triInput, triBefore, Word.toBitVec, Word.value, limbBase]

/-- Three aliased maximal operands require low/high carries of two and a
    wrapping result. The complete imported row produces the native state effects. -/
example : UnifiedReduced.TriAdd.spec triInput ⟨⟨65533, 65535⟩, ⟨2, 3⟩⟩ := by
  apply UnifiedReduced.TriAdd.babyBear_soundness zeroSetup triInput _ triRow
  refine ⟨?_, tri_satisfies, ?_⟩
  · constructor
    · rfl
    · rfl
    · intro _
      repeat' apply And.intro
      all_goals decide
    · decide
    · exact tri_contract
  · constructor
    · intro _
      repeat' apply And.intro
      all_goals rfl
    all_goals rfl

private def triDiscarded : UnifiedReduced.TriAdd.Input :=
  { triInput with rd := zeroRegister, before := before }

private theorem tri_discarded_contract : UnifiedReduced.TriAdd.RegisterContract triDiscarded := by
  constructor
  · refine ⟨123, ?_, ?_⟩
    · apply read_register
      simp [triDiscarded, triInput, before, Std.ExtDHashMap.get?_insert]
    · simp [triDiscarded]
  · refine ⟨123, ?_, ?_⟩
    · apply read_register
      simp [triDiscarded, triInput, before, Std.ExtDHashMap.get?_insert]
    · simp [triDiscarded]
  · refine ⟨0, ?_, ?_⟩
    · rfl
    · simp [triDiscarded]
  · apply read_register
    simp [triDiscarded, triInput, before, Word.toBitVec, Word.value, limbBase]

example : UnifiedReduced.TriAdd.spec triDiscarded ⟨⟨0, 0⟩, ⟨2, 3⟩⟩ := by
  apply UnifiedReduced.TriAdd.babyBear_soundness zeroSetup triDiscarded _ row
  refine ⟨?_, satisfies, ?_⟩
  · constructor
    · rfl
    · rfl
    · simp [triDiscarded]
    · decide
    · exact tri_discarded_contract
  · constructor
    · simp [triDiscarded]
    all_goals rfl

open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def nativeAssignment (rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 || i = 40 then (if rollover then 524284 else 4)
  else if i = 3 || i = 41 || i = 47 then (if rollover then 7 else 0)
  else if i = 32 then (if rollover then 0 else 8)
  else if i = 33 then (if rollover then 8 else 0)
  else if i = 46 then (if rollover then 524285 else 5)
  else if i = 48 then 123
  else if i = 131 || i = 132 || i = 133 then 1
  else aliasedRow i

private theorem native_constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (nativeAssignment rollover))
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) := by
  apply Verification.holds_append (left := Airbender.UnifiedReduced.importedConstraints zeroSetup)
    (right := Airbender.UnifiedReduced.importedConstraintsTimestampLookups)
  · cases rollover <;>
      simpa [Airbender.UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment,
        Verification.range16, nativeAssignment, aliasedRow, row,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
        show (14745600 : ZMod babyBearModulus) * (524284 + 4) * (524284 + 4) +
          3840 * (524284 + 4) = 0 by decide,
        show (8 : ZMod babyBearModulus) + -7 + 3840 * (524284 + 4) = 0 by decide]
        using aliased_satisfies
  · cases rollover <;>
      simp [Airbender.UnifiedReduced.importedConstraintsTimestampLookups,
        FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, nativeAssignment, aliasedRow, row]
    all_goals decide

private def nativeToken (timeLo timeHi value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register 1).addressCode, (timeLo, timeHi), Nat.pair value 0⟩

private def nativeTrace (rollover : Bool) : UnifiedTrace babyBearModulus where
  rows := [⟨.machine, nativeAssignment rollover⟩]
  rom := zeroSetup
  initial := ⟨(65534, 2), (if rollover then 524284 else 4, if rollover then 7 else 0)⟩
  terminal := ⟨(2, 3), (if rollover then 0 else 8, if rollover then 8 else 0)⟩
  initialMemory := [nativeToken 0 0 123]
  terminalMemory := [nativeToken (if rollover then 524286 else 6) (if rollover then 7 else 0) 246]

private theorem native_accepted (rollover : Bool) : Accepted (nativeTrace rollover) := by
  constructor
  · intro current member
    simp only [nativeTrace, List.mem_singleton] at member
    subst current
    exact native_constraints rollover
  · intro current member
    simp only [nativeTrace, List.mem_singleton] at member
    subst current
    rfl
  · change [(nativeTrace rollover).initial, (nativeTrace rollover).terminal].Perm
      [(nativeTrace rollover).terminal, (nativeTrace rollover).initial]
    exact List.Perm.swap _ _ []
  · cases rollover <;> decide

private theorem native_boundary (rollover : Bool) : ClockBoundary (nativeTrace rollover) := by
  constructor
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro token member
    simp only [nativeTrace, List.mem_singleton] at member
    subst token
    constructor <;> decide

private theorem native_image (rollover : Bool) :
    initialImage before [Cell.register 1] = some (nativeTrace rollover).initialMemory := by
  have read : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, List.mapM_cons, List.mapM_nil, read]
  rfl

theorem native_clock_effects (rollover : Bool) :
    ∀ current ∈ (nativeTrace rollover).rows, ClockEffects current.columns current.assignment :=
  Airbender.UnifiedReduced.native_clocks (by decide) (by decide)
    (native_accepted rollover) (native_boundary rollover)

theorem initialized_word_bounds (rollover : Bool) :
    (∀ current ∈ (nativeTrace rollover).rows, ∀ port ∈ current.ports,
      (readToken current.assignment port).word.Bounded) ∧
    (∀ current ∈ (nativeTrace rollover).rows, ∀ port ∈ current.ports,
      (writeToken current.columns current.assignment port).word.Bounded) ∧
    (∀ token ∈ (nativeTrace rollover).terminalMemory, token.word.Bounded) :=
  Airbender.UnifiedReduced.native_value_bounds (by decide) (by decide)
    (native_accepted rollover) (native_boundary rollover) (native_image rollover)

private def fabricatedAssignment (i : Nat) : ZMod babyBearModulus :=
  if i = 42 then 124
  else if i = 50 then 247
  else if i = 80 then 123 * 124 * 943718400
  else nativeAssignment false i

private def fabricatedTrace : UnifiedTrace babyBearModulus :=
  { (nativeTrace false) with
    rows := [⟨.machine, fabricatedAssignment⟩]
    terminalMemory := [nativeToken 6 0 247] }

theorem fabricated_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment fabricatedAssignment)
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) := by
  apply Verification.holds_append (left := Airbender.UnifiedReduced.importedConstraints zeroSetup)
    (right := Airbender.UnifiedReduced.importedConstraintsTimestampLookups)
  · simp [Airbender.UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, fabricatedAssignment, nativeAssignment,
      aliasedRow, row, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (exact ⟨⟨0, by decide⟩, rfl⟩)
  · simp [Airbender.UnifiedReduced.importedConstraintsTimestampLookups,
      FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, fabricatedAssignment,
      nativeAssignment, aliasedRow, row]
    all_goals decide

theorem fabricated_read_rejected : ¬ Accepted fabricatedTrace := by
  intro accepted
  have impossible : ¬ (fabricatedTrace.initialMemory ++ fabricatedTrace.rows.flatMap Row.writes).Perm
      (fabricatedTrace.terminalMemory ++ fabricatedTrace.rows.flatMap Row.reads) := by decide
  exact impossible accepted.memory

theorem initialized_read_history (rollover : Bool) :
    ∃ history, MemoryHistory (nativeTrace rollover) history :=
  Airbender.UnifiedReduced.native_memory_history (by decide) (by decide)
    (native_accepted rollover) (native_boundary rollover) (native_image rollover) (by decide)

end Tests.UnifiedReduced
