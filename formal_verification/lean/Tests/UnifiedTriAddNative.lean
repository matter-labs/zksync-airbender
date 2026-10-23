import Tests.Platform
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.Sail.WordMemoryState

set_option Elab.async false

namespace Tests.UnifiedTriAddNative
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

local instance : Sail.ArchSem.MemoryPlatform SailRV32.exception := Tests.upstreamPlatform

private def setup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private def assignment : Nat → ZMod babyBearModulus
  | 4 | 5 | 6 | 7 | 20 | 38 | 44 | 129 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 | 40 => 4
  | 32 => 8
  | 46 => 5
  | 36 | 42 | 48 => 123
  | 50 => 369
  | 80 => 123 * 123 * 943718400
  | _ => 0

private def before : State :=
  wordWriteState { (default : State) with
    regs := (default : State).regs.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32) }
    0 0xc210c0f3

private def cells : List Cell := [.register 1]
private def row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩
private def trace : UnifiedTrace babyBearModulus where
  rows := [row]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := [Cell.initialToken (.register 1) 123]
  terminalMemory := [⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 369 0⟩]
private def entry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0xc210c0f3, .ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1),
    ⟨.machine, 1, 1, 1, ⟨0, 0⟩, 512, 0⟩⟩

private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (clockConstraints setup) := by
  apply Verification.holds_append
  · simp [importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
    all_goals solve
      | decide
      | (apply Verification.range16_contains; decide)
      | (exact ⟨⟨0, by decide⟩, rfl⟩)
  · simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment]
    all_goals decide

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem decoded : Decoded trace [entry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 1, _
  exact ⟨0, by decide⟩

private theorem inputs : NativeInputs customDecoderFields trace before cells [entry] := by
  refine ⟨by decide, ?_, ?_, ?_, ⟨[0], ?_⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    subst cell
    trivial
  · have read : (Cell.register 1).read before = .ok 123 before := by
      apply read_register
      simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, read]
    rfl
  · refine ⟨(4, 0), ?_⟩
    have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
      apply read_register
      simp [before, wordWriteState]
    simp [initialState, pc, trace, PCState.boundary]
  · have bytes : (Cell.ram 0).read before = .ok 0xc210c0f3 before :=
      written_word_read _ _ _
    have original : run (SailRV32.Functions.encdec_backwards 0xc210c0f3) before =
        .ok (.ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1)) before := by
      with_unfolding_all rfl
    simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, original,
      customDecoderFields, bind, Option.bind, pure]
    rfl
  · constructor
    · constructor <;> decide
    · decide
    · intro token member
      have same := List.mem_singleton.mp member
      subst token
      constructor <;> decide

def output : Output := ⟨⟨369, 0⟩, ⟨4, 0⟩⟩

theorem actual_native_triadd :
    ∃ input : TriAdd.Input, TriAdd.TraceMapping trace before cells [entry] input output assignment ∧
      TriAdd.spec input output := by
  obtain ⟨state, position⟩ := UnifiedReduced.Proofs.custom_row_position_exists
    (row := row) (by decide) (by decide) accepted inputs decoded (by simp [trace])
  let input : TriAdd.Input := ⟨⟨123, 0⟩, ⟨123, 0⟩, ⟨123, 0⟩,
    .Regidx 1, .Regidx 1, .Regidx 1, ⟨0, 0⟩, state⟩
  have mapping : TriAdd.TraceMapping trace before cells [entry] input output assignment := by
    refine ⟨?_, position, entry, by simp, ?_, rfl⟩
    · constructor
      · rw [TriAdd.leftOperand, Trace.Proofs.read_word]
        change Word.mk 123 0 = Word.mk (123 : ZMod babyBearModulus).val (0 : ZMod babyBearModulus).val
        decide
      · rw [TriAdd.rightOperand, Trace.Proofs.read_word]
        change Word.mk 123 0 = Word.mk (123 : ZMod babyBearModulus).val (0 : ZMod babyBearModulus).val
        decide
      · rw [TriAdd.oldDestination, Trace.Proofs.read_word]
        change Word.mk 123 0 = Word.mk (123 : ZMod babyBearModulus).val (0 : ZMod babyBearModulus).val
        decide
      all_goals rfl
    · decide
  exact ⟨input, mapping, TriAdd.soundness (by decide) (by decide)
    trace before cells [entry] input output assignment
    ⟨⟨inputs⟩, ⟨accepted, decoded, by simp [trace, row]⟩, mapping⟩⟩

end Tests.UnifiedTriAddNative
