import Tests.TraceExecution
import Slop.UnifiedReduced.Claims
import Slop.Sail.WordMemoryState

namespace Tests.UnifiedMixedExecution
open Airbender Arithmetic UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 5000000

private def before : State :=
  wordWriteState (wordWriteState (wordWriteState
    { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32) }
    0 0x00108093) 4 0xc210c0f3) 8 0x2083
private def cells : List Cell := Tests.TraceExecution.cells ++ [.ram 0]
private def program : List UnifiedReduced.ProgramEntry := [
  ⟨0, 0x00108093, .ITYPE (1, .Regidx 1, .Regidx 1, .ADDI), ⟨.machine, 1, 0, 1, ⟨1, 0⟩, 1, 0⟩⟩,
  ⟨4, 0xc210c0f3, .ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1),
    ⟨.machine, 1, 1, 1, ⟨0, 0⟩, 512, 0⟩⟩,
  ⟨8, 0x2083, .LOAD (0, .Regidx 0, .Regidx 1, false, 4),
    ⟨.machine, 0, 0, 1, ⟨0, 0⟩, 131072, 0⟩⟩]
private def arithmetic : Nat → ZMod babyBearModulus
  | 4 | 5 | 7 | 8 | 11 | 44 | 50 | 129 | 130 | 131 | 132 | 133 => 1
  | 2 | 30 | 46 => 4
  | 32 => 8
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
private def load : Nat → ZMod babyBearModulus
  | 4 | 7 | 28 | 44 | 54 | 87 | 129 | 130 | 131 | 132 | 133 => 1
  | 0 => 8
  | 2 | 30 => 12
  | 32 | 51 | 91 => 16
  | 34 => 5
  | 46 => 10
  | 48 => 3
  | 50 | 90 => 0x8093
  | 86 => 65472
  | 88 => 34
  | _ => 0
private def trace (value : Nat) : UnifiedTrace babyBearModulus where
  rows := [⟨.machine, load⟩, ⟨.machine, triadd value⟩, ⟨.machine, arithmetic⟩]
  rom := UnifiedReduced.Setup.table before
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 12 (16, 0)
  initialMemory := Trace.ROMView.nativeBootImage cells
  terminalMemory := [⟨(Cell.register 0).addressCode, (12, 0), 0⟩,
    ⟨(Cell.register 1).addressCode, (14, 0), Nat.pair 0x8093 16⟩] ++
    (Trace.ROMView.nativeBootImage (p := babyBearModulus) Tests.TraceExecution.cells).drop 2 ++
    [⟨(Cell.ram 0).addressCode, (13, 0), 0⟩]

private theorem public_bytes :
    (Cell.ram 0).read before = .ok 0x00108093 before ∧
    (Cell.ram 4).read before = .ok 0xc210c0f3 before ∧
    (Cell.ram 8).read before = .ok 0x2083 before := by
  refine ⟨?_, ?_, written_word_read _ _ _⟩
  · exact written_word_disjoint 8 0x2083 (Or.inl (by decide))
      (written_word_disjoint 4 0xc210c0f3 (Or.inl (by decide)) (written_word_read _ _ _))
  · exact written_word_disjoint 8 0x2083 (Or.inl (by decide)) (written_word_read _ _ _)

theorem original_mixed_public_image : Mixed.programImage before [0, 4, 8] = some program := by
  have standard : run (SailRV32.Functions.encdec_backwards 0x00108093) before =
      .ok (.ITYPE (1, .Regidx 1, .Regidx 1, .ADDI)) before := by with_unfolding_all rfl
  have custom : run (SailRV32.Functions.encdec_backwards 0xc210c0f3) before =
      .ok (.ZIMOP_MOP_RR (4, .Regidx 1, .Regidx 1, .Regidx 1)) before := by with_unfolding_all rfl
  have memory : run (SailRV32.Functions.encdec_backwards 0x2083) before =
      .ok (.LOAD (0, .Regidx 0, .Regidx 1, false, 4)) before := by with_unfolding_all rfl
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, public_bytes.1, public_bytes.2.1,
    public_bytes.2.2, standard, custom, memory, bind, Option.bind, pure]
  rfl

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, wordWriteState, Tests.TraceExecution.before,
          Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem configuration : Configured before := by
  have written : run (SailRV32.Functions.wX_bits (.Regidx 1) 0) Tests.TraceExecution.before =
      .ok () { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 0 } := by
    simp only [SailRV32.Functions.wX_bits, SailRV32.Functions.wX,
      SailRV32.Functions.regval_into_reg, write_callback_pure]
    exact run_bind_of_ok _ _ _ _ _ (write_register .x1 0 Tests.TraceExecution.before)
  have preserved := configuration_gpr_write Tests.TraceExecution.configuration 1 0 written
  exact configuration_register_frame (before := { Tests.TraceExecution.before with
      regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32) }) (after := before) rfl preserved

private theorem inputs : Mixed.Inputs (trace 1) before cells program := by
  constructor
  · refine ⟨by decide, ?_, ?_, ?_, rfl, rfl, ⟨[0, 4, 8], original_mixed_public_image⟩, rfl⟩
    · intro cell member
      simp [cells, Tests.TraceExecution.cells] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
    · refine ⟨?_, zero_registers, ?_⟩
      · apply read_register
        simp [before, wordWriteState, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
      · intro address member bound
        have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
        subst address
        change 4194304 ≤ 0 at bound
        omega
    · refine ⟨Trace.ROMView.nativeBootImage Tests.TraceExecution.cells ++ [Cell.initialToken (.ram 0) 0x00108093], ?_⟩
      simp only [initialImage, cells, Tests.TraceExecution.cells, List.cons_append, List.nil_append,
        List.mapM_cons, List.mapM_nil, zero_registers, public_bytes.1, bind, Option.bind]
      rfl
  · intro index
    have numeric : ∀ n : Nat, n < 32 → Cell.register (BitVec.ofNat 5 n) ∈ cells := by
      intro n bound
      interval_cases n <;> simp [cells, Tests.TraceExecution.cells]
    simpa using numeric index.toNat index.isLt
  · intro entry member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · exact configuration
  · intro address member
    have zero : address = 0 := by simpa [cells, Tests.TraceExecution.cells] using member
    subst address
    unfold OrdinaryWordAddress
    decide
  · rintro ⟨entry, member, imm, rs1, rd, encoding⟩
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> cases encoding
  · intro entry member imm rs1
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp

private theorem public_word : ROM.words before 0 = 0x00108093 := by
  change (match (Cell.ram 0).read before with | .ok value _ => value | .error _ _ => 0) = _
  rw [public_bytes.1]

private theorem constraints (kind : Fin 4) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if kind = 0 then arithmetic else if kind = 1 then load
      else triadd (if kind = 2 then 1 else 2))) (clockConstraints (trace 1).rom) := by
  fin_cases kind
  all_goals apply Verification.holds_append
  all_goals first
    | (simp [importedConstraints, trace, FlatOperation.ConstraintsHoldFlat,
        Verification.environment, Expression.eval, arithmetic, triadd, load, Lookup.Contains, Table.toRaw, fromElements]
       repeat' apply And.intro
       all_goals solve
         | decide
         | (apply Verification.range16_contains; decide)
         | (exact ⟨⟨0, by decide⟩, by with_unfolding_all decide⟩)
         | (refine ⟨⟨1048961, by decide⟩, ?_⟩
            change _ = (#v[0, (Word.ofBitVec (ROM.words before 0)).lo,
              (Word.ofBitVec (ROM.words before 0)).hi, 0, 0, 0, 0, 0, 0, 34] : Vector Nat 10).map
                (fun (n : Nat) => (n : ZMod babyBearModulus))
            rw [public_word]
            with_unfolding_all decide))
    | (simp [importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
       repeat' apply And.intro
       all_goals apply Trace.Proofs.range_contains
       all_goals simp [Expression.eval, Verification.environment, arithmetic, triadd, load]
       all_goals decide)

private theorem accepted : Accepted (trace 1) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact constraints 1
    · exact constraints 2
    · exact constraints 0
  · intro actual member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · exact (List.Perm.swap _ _ _).trans (List.Perm.cons _
      ((List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))))
  · decide +kernel

private theorem decoded : UnifiedReduced.Decoded (trace 1) program := by
  intro actual member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change ∃ i : Fin 3, _
    exact ⟨2, by decide +kernel⟩
  · change ∃ i : Fin 3, _
    exact ⟨1, by decide +kernel⟩
  · change ∃ i : Fin 3, _
    exact ⟨0, by decide +kernel⟩

theorem sail_complete_mixed_trace  :
    Realizes (Mixed.Step program) (trace 1) before cells (Trace.ROMView.token before) :=
  Mixed.execution_soundness (by decide) (by decide) (by decide) inputs accepted decoded

theorem fabricated_custom_read_locally_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (triadd 2)) (clockConstraints (trace 1).rom) := constraints 3

theorem fabricated_custom_read_breaks_matching :
    ¬((trace 2).initialMemory ++ (trace 2).memorySteps.map Prod.snd).Perm
      ((trace 2).terminalMemory ++ (trace 2).memorySteps.map Prod.fst) := by decide +kernel

end Tests.UnifiedMixedExecution
