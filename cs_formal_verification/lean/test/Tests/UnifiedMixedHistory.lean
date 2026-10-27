import Slop.Sail.ResetState
import Slop.UnifiedReduced.Claims
import Slop.Sail.WordMemoryState

namespace Tests.UnifiedMixedHistory
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def setup : Table (ZMod babyBearModulus) (fields 10) := .fromStatic {
  name := "UnifiedDisabledQueries"
  length := 1
  row _ := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  index _ := 0
  Spec x := ∃ i : Fin 1, x = (fun (_ : Fin 1) => #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) i
  contains_iff _ := Iff.rfl
}
private def arithmetic : Nat → ZMod babyBearModulus
  | 4 | 5 | 7 | 8 | 11 | 44 | 129 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 | 46 => 4
  | 32 => 8
  | 36 | 48 => 123
  | 50 => 124
  | _ => 0
private def triadd (value : Nat) : Nat → ZMod babyBearModulus
  | 4 | 5 | 6 | 7 | 20 | 38 | 44 | 129 | 130 | 131 | 132 | 133 => 1
  | 0 => 4
  | 2 | 30 | 40 => 8
  | 32 => 12
  | 34 => 6
  | 46 => 9
  | 36 | 42 | 48 => value
  | 50 => 3 * value
  | 80 => value * value * 943718400
  | _ => 0
private def standardRow : Row babyBearModulus UnifiedFamily := ⟨.machine, arithmetic⟩
private def customRow (value : Nat) : Row babyBearModulus UnifiedFamily := ⟨.machine, triadd value⟩
private def cells : List Cell := [.register 1, .register 0]
private noncomputable def before : State :=
  wordWriteState (wordWriteState { resetMachine with
    regs := resetMachine.regs.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32) }
    0 0x00108093) 4 0xc210c0f3

theorem airbender_before : Configured before := by
  configured_fixture [before, wordWriteState]

private noncomputable def program : List UnifiedReduced.ProgramEntry := [
  ⟨0, 0x00108093, .ITYPE (1, .Regidx 1, .Regidx 1, .ADDI), ⟨.machine, 1, 0, 1, ⟨1, 0⟩, 1, 0⟩⟩,
  ⟨4, 0xc210c0f3, .ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1),
    ⟨.machine, 1, 1, 1, ⟨0, 0⟩, 512, 0⟩⟩]
private def trace (value : Nat) : UnifiedTrace babyBearModulus where
  rows := [customRow value, standardRow]
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 8 (12, 0)
  initialMemory := [(.register 1 : Cell).initialToken 123, (.register 0 : Cell).initialToken 0]
  terminalMemory := [⟨(Cell.register 1).addressCode, (10, 0), Nat.pair (3 * value) 0⟩,
    ⟨(Cell.register 0).addressCode, (5, 0), 0⟩]

private theorem constraints (value : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if value = 0 then arithmetic else triadd (if value = 1 then 124 else 125))) (clockConstraints setup) := by
  fin_cases value
  all_goals apply Verification.holds_append
  all_goals first
    | (simp [importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Verification.environment, Expression.eval, arithmetic, triadd, Lookup.Contains, Table.toRaw, fromElements]
       repeat' apply And.intro
       all_goals solve
         | decide
         | (apply Verification.range16_contains; decide)
         | (exact ⟨⟨0, by decide⟩, rfl⟩))
    | (simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
       repeat' apply And.intro
       all_goals apply Trace.Proofs.range_contains
       all_goals simp [Expression.eval, Verification.environment, arithmetic, triadd]
       all_goals decide)

private theorem accepted : Accepted (trace 124) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact constraints 1
    · exact constraints 0
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · decide +kernel

private theorem decoded : UnifiedReduced.Decoded (trace 124) program := by
  intro actual member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · change ∃ i : Fin 2, _
    exact ⟨1, by decide +kernel⟩
  · change ∃ i : Fin 2, _
    exact ⟨0, by decide +kernel⟩

theorem original_mixed_public_image : Mixed.programImage before [0, 4] = some program := by
  have first : (Cell.ram 0).read before = .ok 0x00108093 before :=
    written_word_disjoint 4 0xc210c0f3 (Or.inl (by decide)) (written_word_read _ 0 0x00108093)
  have second : (Cell.ram 4).read before = .ok 0xc210c0f3 before := written_word_read _ _ _
  have standard : Airbender.Reference.RiscV.Sail.decodeOnReset 0x00108093 = some (.ITYPE (1, .Regidx 1, .Regidx 1, .ADDI)) :=
    by decode_on_reset
  have custom : Airbender.Reference.RiscV.Sail.decodeOnReset 0xc210c0f3 = some (.ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1)) :=
    by decode_on_reset
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, first, second, standard, custom,
    bind, Option.bind, pure]
  rfl

private theorem inputs : NativeInputs Mixed.decoderFields (trace 124) before cells program := by
  refine ⟨by decide, ?_, ?_, ?_, ⟨[0, 4], original_mixed_public_image⟩, ?_, airbender_before⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
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
  · constructor
    · constructor <;> decide
    · decide
    · intro token member
      simp [trace] at member
      rcases member with rfl | rfl <;> constructor <;> decide

theorem actual_mixed_memory : MemoryExecution (trace 124) before cells :=
  Mixed.native_memory_execution (by decide) (by decide) inputs accepted decoded

theorem final_dependency : ∃ after, (Cell.register 1).read after = .ok 372 after := by
  obtain ⟨history, rows, after, consistent, permutation, ordered, native, matched⟩ := actual_mixed_memory
  have final := Trace.Proofs.terminal_sail_reads (by decide) (by decide) accepted inputs.clocks
    inputs.image inputs.distinct consistent matched
  obtain ⟨cell, present, address, read⟩ := final (trace 124).terminalMemory[0] (by simp [trace])
  have same : cell = Cell.register 1 := Trace.Proofs.cell_address_injective address
  subst cell
  have value : Trace.memoryWord (trace 124).terminalMemory[0].value = (372 : BitVec 32) := by decide +kernel
  exact ⟨after, value ▸ read⟩

theorem fabricated_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (triadd 125)) (clockConstraints setup) := constraints 2

theorem fabricated_custom_read_breaks_matching :
    ¬((trace 125).initialMemory ++ (trace 125).memorySteps.map Prod.snd).Perm
      ((trace 125).terminalMemory ++ (trace 125).memorySteps.map Prod.fst) := by decide +kernel

end Tests.UnifiedMixedHistory
