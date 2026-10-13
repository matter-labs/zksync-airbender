import Airbender.Review.UnifiedReduced.Theorems
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def literal (upper : Bool) : UnifiedReduced.Caller.ControlLiteral :=
  if upper then .lui 128 else .addi 128
private def bits (upper : Bool) : BitVec 32 := if upper then 0x00080637 else 0x08000613
private def low (upper : Bool) : Nat := if upper then 0 else 128
private def high (upper : Bool) : Nat := if upper then 8 else 0
private def entry (upper : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, bits upper, (literal upper).instruction 12,
    ⟨.machine, 0, 0, 12, ⟨low upper, high upper⟩, 1, 0⟩⟩
private def initialState : State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x12 (65537 : BitVec 32)
  mem := Std.ExtHashMap.emptyWithCapacity
  tags := ()
  cycleCount := 0
  sailOutput := #[]
private def before (upper : Bool) : State := wordWriteState initialState 0 (bits upper)
private def cells : List Cell := [.register 0, .register 12]
private def assignment (upper : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 || column = 30 || column = 40 then 4
  else if column = 32 then 8
  else if column = 7 || column = 44 then 12
  else if column = 8 || column = 50 then low upper
  else if column = 9 || column = 51 then high upper
  else if column = 4 || column = 11 || column = 48 || column = 49 ||
      column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else 0
private def row (upper : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, assignment upper⟩
private def data (upper : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [row upper]
    rom := UnifiedReduced.Setup.table (before upper)
    initial := (row upper).start
    terminal := (row upper).finish
    initialMemory := [⟨(Cell.register 0).addressCode, (0, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 1 1⟩]
    terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (low upper) (high upper)⟩] }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, [], [], []⟩
  program := []

private theorem core (upper : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment upper))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before upper))) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (cases upper <;> decide +kernel)
    | (apply Verification.range16_contains; cases upper <;> decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem timestamps (upper : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment upper)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases upper <;> decide +kernel

private theorem accepted (upper : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (data upper) [entry upper] := by
  constructor
  · constructor
    · intro current member
      have same : current = row upper := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append (core upper) (timestamps upper)
    · intro current member
      have same : current = row upper := List.mem_singleton.mp member
      subst current
      cases upper <;> decide +kernel
    · exact List.Perm.swap _ _ []
    · intro current member
      have empty : (data upper).callers = [] := by cases upper <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (data upper).calls = [] := by cases upper <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same : current = row upper := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, (row upper).decoderQuery = ([entry upper].get i).query
    refine ⟨0, ?_⟩
    cases upper <;> decide +kernel
  · cases upper <;> decide +kernel

private theorem initialized (upper : Bool) : initialImage (before upper) cells = some (data upper).machine.initialMemory := by
  have control : (Cell.register 12).read (before upper) = .ok 65537 (before upper) := by
    apply rX_register_frame (before := initialState) (after := before upper) rfl 12
    apply read_register
    simp [initialState]
  have zero : (Cell.register 0).read (before upper) = .ok 0 (before upper) := by
    with_unfolding_all rfl
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  cases upper <;> rfl

private theorem program_image (upper : Bool) : UnifiedReduced.Mixed.programImage (before upper) [0] = some [entry upper] := by
  have bytes : (Cell.ram 0).read (before upper) = .ok (bits upper) (before upper) := written_word_read initialState 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards (bits upper)) (before upper) =
      .ok ((literal upper).instruction 12) (before upper) := by
    cases upper <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields ((literal upper).instruction 12) = some (entry upper).data := by
    cases upper <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem inputs (upper : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (data upper) [entry upper] (before upper) [] [0] cells := by
  refine ⟨⟨rfl, ?_, ?_⟩, program_image upper, initialized upper, ?_, ?_, rfl, rfl, ?_⟩
  · constructor <;> cases upper <;> decide +kernel
  · cases upper <;> decide +kernel
  · decide +kernel
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem preparation (upper : Bool) :
    UnifiedReduced.Caller.ControlPreparation (data upper) [entry upper] 8 12 (literal upper) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro current member
    have same : current = entry upper := List.mem_singleton.mp member
    subst current
    rfl
  · cases upper <;> decide +kernel
  · cases upper <;> decide +kernel
  · cases upper <;> decide +kernel

theorem literal_prepares_actual_control (upper : Bool) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (data upper) (before upper) cells 8 12 (literal upper) :=
  UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (accepted upper) (inputs upper) (preparation upper) (by decide) (by decide)

theorem initial_control_is_different (upper : Bool) :
    (Cell.register 12).read (before upper) = .ok 65537 (before upper) ∧ (literal upper).value ≠ 65537 := by
  constructor
  · apply rX_register_frame (before := initialState) (after := before upper) rfl 12
    apply read_register
    simp [initialState]
  · cases upper <;> decide +kernel

theorem wrong_preparation_instruction_rejected :
    ¬ UnifiedReduced.Caller.ControlPreparation (data false) [entry false] 8 12 (.addi 0) := by
  intro scope
  have mismatch := scope.program (entry false) (List.mem_singleton_self _)
  have impossible : (128 : BitVec 12) = 0 := by
    simpa only [entry, literal, Bool.false_eq_true, if_false, UnifiedReduced.Caller.ControlLiteral.instruction,
      SailRV32.instruction.ITYPE.injEq, Prod.mk.injEq, and_true, true_and] using mismatch
  exact (by decide : (128 : BitVec 12) ≠ 0) impossible

end Tests.ControlPreparation
