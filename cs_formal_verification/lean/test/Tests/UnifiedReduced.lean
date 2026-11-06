import Slop.Sail.ResetState
import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.Arith
import Slop.BabyBear
import Slop.Sail.WordMemoryState

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

private theorem zeroSetup_zero : UnifiedReduced.Completeness.ZeroRow zeroSetup := by
  intro env entry h
  change ∃ i : Fin 1, entry.map (Expression.eval env) = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  exact ⟨0, h.trans (by decide)⟩

private def rowWitness : UnifiedReduced.Completeness.Arith :=
  ⟨⟨65532, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
private def row : Nat → ZMod babyBearModulus := rowWitness.honest

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

example : (Word.mk (row 30).val (row 31).val).toBitVec = (Word.mk 65532 2).toBitVec + 4 := by
  have result := UnifiedReduced.Proofs.pc_successor (p := babyBearModulus)
    (initial := ⟨65532, 2⟩) (final := ⟨(row 30).val, (row 31).val⟩)
    (by decide) satisfies rfl ⟨rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl⟩ ⟨by decide, by decide⟩
  exact result.2.2

example : (∑ i : Fin 18, (row UnifiedReduced.Variables.dispatchColumns[i]).val) ≤ 1 :=
  UnifiedReduced.Proofs.dispatch_count (by decide) satisfies rfl


open Airbender.Reference.RiscV
open Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail

private def aliasedWitness : UnifiedReduced.Completeness.Arith :=
  { rowWitness with rs1 := 1, rs2 := 1, rd := 1, aLo := 123, bLo := 123 }
private def aliasedRow : Nat → ZMod babyBearModulus := aliasedWitness.honest

private theorem aliased_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment aliasedRow)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

private def before : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (196604 : BitVec 32)) }

private def input : Input where
  row := ⟨.add, ⟨123, 0⟩, ⟨123, 0⟩, ⟨0, 0⟩, ⟨65532, 2⟩⟩
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
example : spec input ⟨⟨246, 0⟩, ⟨0, 3⟩⟩ := by
  apply UnifiedReduced.Proofs.standard_soundness (by decide) zeroSetup input _ aliasedRow
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
    row := ⟨.addi, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨65532, 2⟩⟩
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
example : spec discarded ⟨⟨0, 0⟩, ⟨0, 3⟩⟩ := by
  apply UnifiedReduced.Proofs.standard_soundness (by decide) zeroSetup discarded _ row
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

private def triWitness : UnifiedReduced.Completeness.Arith :=
  ⟨rowWitness.frame, 3, 1, 1, 1, 65535, 65535, 65535, 65535, 0, 0, 65535, 65535⟩
private def triRow : Nat → ZMod babyBearModulus := triWitness.honest

private theorem tri_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment triRow)
      (UnifiedReduced.importedConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete_core _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

private def triBefore : State :=
  { (default : State) with regs :=
    ((default : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (4294967295 : BitVec 32) |>.insert .PC (196604 : BitVec 32)) }

private def triInput : UnifiedReduced.TriAdd.Input where
  left := ⟨65535, 65535⟩
  right := ⟨65535, 65535⟩
  oldDestination := ⟨65535, 65535⟩
  rs1 := .Regidx 1
  rs2 := .Regidx 1
  rd := .Regidx 1
  pc := ⟨65532, 2⟩
  before := triBefore

private theorem tri_contract : UnifiedReduced.TriAdd.Calculation.RegisterContract triInput := by
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
example : UnifiedReduced.TriAdd.spec triInput ⟨⟨65533, 65535⟩, ⟨0, 3⟩⟩ := by
  apply UnifiedReduced.Proofs.triadd_soundness (by decide) zeroSetup triInput _ triRow
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

private theorem tri_discarded_contract : UnifiedReduced.TriAdd.Calculation.RegisterContract triDiscarded := by
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

example : UnifiedReduced.TriAdd.spec triDiscarded ⟨⟨0, 0⟩, ⟨0, 3⟩⟩ := by
  apply UnifiedReduced.Proofs.triadd_soundness (by decide) zeroSetup triDiscarded _ row
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

private def nativeWitness (rollover : Bool) : UnifiedReduced.Completeness.Arith :=
  { aliasedWitness with
    frame := ⟨65532, 2, if rollover then 524284 else 4, if rollover then 7 else 0, 0, 0,
      if rollover then 524284 else 4, if rollover then 7 else 0,
      if rollover then 524285 else 5, if rollover then 7 else 0⟩
    oldLo := 123 }
private def nativeAssignment (rollover : Bool) : Nat → ZMod babyBearModulus :=
  (nativeWitness rollover).honest

private theorem native_constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (nativeAssignment rollover))
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) := by
  cases rollover <;>
    exact UnifiedReduced.Completeness.Arith.complete _
      (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

private def nativeToken (timeLo timeHi value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register 1).addressCode, (timeLo, timeHi), Nat.pair value 0⟩

private def nativeTrace (rollover : Bool) : UnifiedTrace babyBearModulus where
  rows := [⟨.machine, nativeAssignment rollover⟩]
  rom := zeroSetup
  initial := ⟨(65532, 2), (if rollover then 524284 else 4, if rollover then 7 else 0)⟩
  terminal := ⟨(0, 3), (if rollover then 0 else 8, if rollover then 8 else 0)⟩
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
  · cases rollover <;> exact List.Perm.swap _ _ []
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

private def fabricatedWitness : UnifiedReduced.Completeness.Arith :=
  { nativeWitness false with bLo := 124 }
private def fabricatedAssignment : Nat → ZMod babyBearModulus := fabricatedWitness.honest

private def fabricatedTrace : UnifiedTrace babyBearModulus :=
  { (nativeTrace false) with
    rows := [⟨.machine, fabricatedAssignment⟩]
    terminalMemory := [nativeToken 6 0 247] }

theorem fabricated_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment fabricatedAssignment)
    (Airbender.UnifiedReduced.clockConstraints zeroSetup) :=
  UnifiedReduced.Completeness.Arith.complete _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ zeroSetup_zero

theorem fabricated_read_rejected : ¬ Accepted fabricatedTrace := by
  intro accepted
  have impossible : ¬ (fabricatedTrace.initialMemory ++ fabricatedTrace.rows.flatMap Row.writes).Perm
      (fabricatedTrace.terminalMemory ++ fabricatedTrace.rows.flatMap Row.reads) := by decide
  exact impossible accepted.memory

theorem initialized_read_history (rollover : Bool) :
    ∃ history, MemoryHistory (nativeTrace rollover) history :=
  Airbender.UnifiedReduced.native_memory_history (by decide) (by decide)
    (native_accepted rollover) (native_boundary rollover) (native_image rollover) (by decide)

private def fetchEntry : Airbender.UnifiedReduced.ProgramEntry :=
  ⟨196604, 0x001080b3, .RTYPE (.Regidx 1, .Regidx 1, .Regidx 1, .ADD),
    ⟨.machine, 1, 1, 1, ⟨0, 0⟩, 1, 0⟩⟩
/-- `before`'s registers on the Airbender reset state. -/
private noncomputable def fetchBefore : State :=
  { Reference.RiscV.Sail.resetMachine with
    regs := Reference.RiscV.Sail.resetMachine.regs.insert .x1 (123 : BitVec 32) |>.insert .PC (196604 : BitVec 32) }
private noncomputable def fetchState : State := wordWriteState fetchBefore fetchEntry.pc.toNat fetchEntry.bits

theorem airbender_fetchState : Reference.RiscV.Sail.Configured fetchState := by
  configured_fixture [fetchState, fetchBefore, wordWriteState]

private theorem fetchImage :
    Airbender.UnifiedReduced.programImage fetchState [fetchEntry.pc] = some [fetchEntry] := by
  have bytes : (Cell.ram fetchEntry.pc).read fetchState = .ok fetchEntry.bits fetchState :=
    written_word_read fetchBefore fetchEntry.pc.toNat fetchEntry.bits
  have decoded : Reference.RiscV.Sail.decodeOnReset fetchEntry.bits = some fetchEntry.instruction := by
    decode_on_reset
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, decoded, bind, Option.bind, pure]
  rfl

theorem accepted_row_fetched (rollover : Bool) :
    Airbender.UnifiedReduced.Fetched (nativeAssignment rollover) fetchState := by
  apply Airbender.UnifiedReduced.fetched (by decide) fetchImage airbender_fetchState
    (Verification.holds_of_sublist (native_constraints rollover) (List.sublist_append_left _ _))
  cases rollover <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

private theorem native_public_inputs (rollover : Bool) :
    NativeInputs Airbender.UnifiedReduced.decoderFields (nativeTrace rollover)
      fetchState [Cell.register 1] [fetchEntry] := by
  constructor
  · decide
  · intro cell member
    simp only [List.mem_singleton] at member
    subst cell
    trivial
  · have read : (Cell.register 1).read fetchState = .ok (123 : BitVec 32) fetchState := by
      apply read_register
      simp [fetchState, wordWriteState, fetchBefore, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, List.mapM_cons, List.mapM_nil, read]
    rfl
  · refine ⟨⟨if rollover then 524284 else 4, if rollover then 7 else 0⟩, ?_⟩
    have pc : run (SailRV32.Functions.get_arch_pc ()) fetchState = .ok 196604 fetchState := by
      apply read_register
      simp [fetchState, wordWriteState, fetchBefore]
    simp only [initialState, pc]
    cases rollover <;> rfl
  · exact ⟨[fetchEntry.pc], fetchImage⟩
  · exact native_boundary rollover
  · exact airbender_fetchState

theorem native_sail_memory_execution (rollover : Bool) :
    Airbender.UnifiedReduced.MemoryExecution (nativeTrace rollover) fetchState [Cell.register 1] := by
  apply Airbender.UnifiedReduced.native_memory_execution (by decide) (by decide)
    (native_accepted rollover) (native_public_inputs rollover)
  intro current member
  simp only [nativeTrace, List.mem_singleton] at member
  subst current
  cases rollover <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

private noncomputable def traceInput : Input :=
  { input with before := Trace.retiredState fetchState (Word.mk 65532 2).toBitVec }

theorem initialized_arithmetic_soundness (rollover : Bool) :
    Sail.spec traceInput ⟨⟨246, 0⟩, ⟨0, 3⟩⟩ := by
  apply Airbender.UnifiedReduced.babyBear_soundness
    (nativeTrace rollover) fetchState [Cell.register 1] [fetchEntry]
    traceInput _ (nativeAssignment rollover)
  refine ⟨?_, ⟨native_accepted rollover, ?_, ?_⟩, ?_⟩
  · constructor
    · exact native_public_inputs rollover
    · intro index source
      have selected : (1 : BitVec 5) = index ∨ (1 : BitVec 5) = index := by
        simpa [traceInput, input] using source
      have same : index = (1 : BitVec 5) := (selected.elim id id).symm
      subst index
      decide
  · intro current member
    simp only [nativeTrace, List.mem_singleton] at member
    subst current
    cases rollover <;> change ∃ i, _
    all_goals exact ⟨⟨0, by decide⟩, by decide⟩
  · simp [nativeTrace]
  · constructor
    · cases rollover <;> constructor <;> rfl
    · refine ⟨[], [], fetchState, ?_, ?_, WriteHistory.nil _, ?_⟩
      · exact List.Perm.refl _
      · simp
      · cases rollover <;> rfl
    · refine ⟨fetchEntry, by simp, ?_, rfl⟩
      cases rollover <;> rfl

end Tests.UnifiedReduced
