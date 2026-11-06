import Slop.Sail.ResetState
import Slop.UnifiedReduced.Claims
import Slop.Sail.WordMemoryState
import Slop.UnifiedReduced.Completeness.Arith

namespace Tests.UnifiedTriAddNative
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384

private def setup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}

private theorem setup_zero : Completeness.ZeroRow setup := by
  intro env entry h
  change ∃ i : Fin 1, entry.map (Expression.eval env) = #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  exact ⟨0, h.trans (by decide)⟩
/-- TRIADD x1 (= x1 + x1 + old x1) at PC 0, clock 4. -/
private def witness : Completeness.Arith :=
  ⟨⟨0, 0, 4, 0, 0, 0, 4, 0, 5, 0⟩, 3, 1, 1, 1, 123, 0, 123, 0, 0, 0, 123, 0⟩
private def assignment : Nat → ZMod babyBearModulus := witness.honest

private noncomputable def before : State :=
  wordWriteState { resetMachine with
    regs := resetMachine.regs.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32) }
    0 0xc210c0f3

theorem airbender_before : Configured before := by
  configured_fixture [before, wordWriteState]

private def cells : List Cell := [.register 1]
private def row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩
private def trace : UnifiedTrace babyBearModulus where
  rows := [row]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 4 (8, 0)
  initialMemory := [Cell.initialToken (.register 1) 123]
  terminalMemory := [⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 369 0⟩]
private noncomputable def entry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0xc210c0f3, .ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1),
    ⟨.machine, 1, 1, 1, ⟨0, 0⟩, 512, 0⟩⟩

private theorem constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) (clockConstraints setup) :=
  Completeness.Arith.complete _
    (by refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide) _ setup_zero

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
  refine ⟨by decide, ?_, ?_, ?_, ⟨[0], ?_⟩, ?_, airbender_before⟩
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
    have original : Airbender.Reference.RiscV.Sail.decodeOnReset 0xc210c0f3 = some (.ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1)) :=
      by decode_on_reset
    simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, original,
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
