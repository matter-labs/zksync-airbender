import Tests.NativeArithmeticSetup
import Airbender.Review.Trace.Families.AddSub.SparseExecution

namespace Tests.SparseArithmeticExecution
open Airbender Trace Reference.Sail Reference.RiscV.Sail

-- All three ports alias x1. Clock-four/five refreshes supply the destination
-- read before its actual clock-six write. PC 24 follows the public UNIMP hole.
private def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 35 then 123 else if i = 47 then 4 else if i = 50 then 5
  else Tests.NativeArithmeticSetup.assignment i
private def nativeRow : Row mersenne31Modulus := ⟨.addSub, assignment⟩
private def cell (time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair 1 0), (time, 0), Nat.pair value 0⟩
private def trace : Data mersenne31Modulus where
  rows := [nativeRow]
  rom := ()
  initial := ⟨(24, 0), (4, 0)⟩
  terminal := ⟨(28, 0), (8, 0)⟩
  initialMemory := [cell 0 123]
  terminalMemory := [cell 6 246]

theorem native_constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    AddSub.importedConstraints := by
  simp [AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, assignment, Tests.NativeArithmeticSetup.assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same : actual = nativeRow := by simpa [trace] using member
    subst actual
    exact native_constraints
  · intro actual member
    have same : actual = nativeRow := by simpa [trace] using member
    subst actual
    decide
  · change [trace.initial, nativeRow.finish].Perm [trace.terminal, nativeRow.start]
    exact List.Perm.swap _ _ []
  · change ([cell 0 123, cell 4 123, cell 5 123, cell 6 246]).Perm
      [cell 6 246, cell 0 123, cell 4 123, cell 5 123]
    decide

private def before : State :=
  { AddSub.NativeSetup.before with regs :=
    ((Std.ExtDHashMap.emptyWithCapacity : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .x1 (123 : BitVec 32) |>.insert .PC (24 : BitVec 32)) }
private def cells : List Cell := [.register 1]

/-- Retain the checked original decoder certificate by framing only public
    register changes. No original Sail decoder is replaced or assumed. -/
theorem decoder_built : AddSub.sparseDecoderSetupImage before 7 20 =
    some AddSub.NativeSetup.setup := by
  have bytes (i : Fin 7) :
      (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
        .ok AddSub.NativeSetup.words[i.val] before :=
    read_word_frame (show before.mem = AddSub.NativeSetup.before.mem from rfl)
      (AddSub.Proofs.native_fixture_words i)
  have slots (i : Fin 7) : programSlotWith decoderFields before (BitVec.ofNat 32 (4 * i.val)) =
      programSlotWith decoderFields AddSub.NativeSetup.before (BitVec.ofNat 32 (4 * i.val)) := by
    unfold programSlotWith
    rw [bytes i, AddSub.Proofs.native_fixture_words i]
  change (([0,4,8,12,16,20,24] : List (BitVec 32)).mapM (programSlotWith decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048569)) = _
  have original := AddSub.Proofs.native_fixture_image
  change (([0,4,8,12,16,20,24] : List (BitVec 32)).mapM
      (programSlotWith decoderFields AddSub.NativeSetup.before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048569)) = _ at original
  have s0 := slots ⟨0, by decide⟩
  have s1 := slots ⟨1, by decide⟩
  have s2 := slots ⟨2, by decide⟩
  have s3 := slots ⟨3, by decide⟩
  have s4 := slots ⟨4, by decide⟩
  have s5 := slots ⟨5, by decide⟩
  have s6 := slots ⟨6, by decide⟩
  change programSlotWith decoderFields before 0 =
    programSlotWith decoderFields AddSub.NativeSetup.before 0 at s0
  change programSlotWith decoderFields before 4 =
    programSlotWith decoderFields AddSub.NativeSetup.before 4 at s1
  change programSlotWith decoderFields before 8 =
    programSlotWith decoderFields AddSub.NativeSetup.before 8 at s2
  change programSlotWith decoderFields before 12 =
    programSlotWith decoderFields AddSub.NativeSetup.before 12 at s3
  change programSlotWith decoderFields before 16 =
    programSlotWith decoderFields AddSub.NativeSetup.before 16 at s4
  change programSlotWith decoderFields before 20 =
    programSlotWith decoderFields AddSub.NativeSetup.before 20 at s5
  change programSlotWith decoderFields before 24 =
    programSlotWith decoderFields AddSub.NativeSetup.before 24 at s6
  simpa only [List.mapM_cons, List.mapM_nil, s0, s1, s2, s3, s4, s5, s6] using original

private theorem inputs : ImageBoundary trace before cells := by
  have source : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok (24 : BitVec 32) before := by
    apply read_register
    simp [before]
  constructor
  · decide
  · simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, source]
    rfl
  · rw [initialState, pc]
    rfl

/-- Full sparse membership selects actual exported slot six at its original PC. -/
theorem decoded : AddSub.SparseDecoded trace AddSub.NativeSetup.setup := by
  intro actual member
  have same : actual = nativeRow := by simpa [trace] using member
  subst actual
  change ∃ i : Fin 1048576, nativeRow.decoderQuery = AddSub.NativeSetup.setup.row i
  refine ⟨⟨6, by decide⟩, ?_⟩
  rw [← AddSub.Proofs.native_exported_rows]
  decide +kernel

theorem initialized_execution : Realizes (SailStep AddSub.NativeSetup.setup.program) trace before cells :=
  sparse_public_sail_execution inputs decoder_built accepted decoded
    (by intro actual member; have same : actual = Cell.register 1 := by simpa [cells] using member
        subst actual; trivial)

/-- Actual fetched/decoded original ADD reaches PC 28 and x1=246. Neither
    the destination read, an intermediate state nor final value is a premise. -/
theorem terminal_values : ∃ after, SailTrace AddSub.NativeSetup.setup.program before after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok (28 : BitVec 32) after ∧
    run (SailRV32.Functions.rX_bits (.Regidx 1)) after = .ok (246 : BitVec 32) after := by
  obtain ⟨after, execution, pc, values⟩ := initialized_execution
  obtain ⟨target, _, address, read⟩ := values (cell 6 246) (by simp [trace])
  have same : target = Cell.register 1 := Trace.Proofs.cell_address_injective address
  subst target
  simp only [id_eq, MemoryToken.word, cell, Nat.unpair_pair] at read
  exact ⟨after, execution, pc, read⟩

end Tests.SparseArithmeticExecution
