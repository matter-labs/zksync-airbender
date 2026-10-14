import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def register (mode : Fin 3) : BitVec 5 := if mode.val = 2 then 10 else 12
private def literal (mode : Fin 3) : UnifiedReduced.Caller.ControlLiteral :=
  if mode.val = 2 then UnifiedReduced.Caller.hashPreparation .keccak
  else if mode.val = 1 then .lui 128 else UnifiedReduced.Caller.hashPreparation (.blakeG true)
private def bits (mode : Fin 3) : BitVec 32 :=
  if mode.val = 2 then 0x00000513 else if mode.val = 1 then 0x00080637 else 0x08000613
private def low (mode : Fin 3) : Nat := if mode.val = 0 then 128 else 0
private def high (mode : Fin 3) : Nat := if mode.val = 1 then 8 else 0
private def entry (mode : Fin 3) : UnifiedReduced.ProgramEntry :=
  ⟨0, bits mode, (literal mode).instruction (register mode),
    ⟨.machine, 0, 0, register mode, ⟨low mode, high mode⟩, 1, 0⟩⟩
private def initialState : State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x12 (65537 : BitVec 32)
    |>.insert .x10 (65537 : BitVec 32)
  mem := Std.ExtHashMap.emptyWithCapacity
  tags := ()
  cycleCount := 0
  sailOutput := #[]
private def before (mode : Fin 3) : State := wordWriteState initialState 0 (bits mode)
private def cells (mode : Fin 3) : List Cell := [.register 0, .register (register mode)]
private def assignment (mode : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 || column = 30 || column = 40 then 4
  else if column = 32 then 8
  else if column = 7 || column = 44 then (register mode).toNat
  else if column = 8 || column = 50 then low mode
  else if column = 9 || column = 51 then high mode
  else if column = 4 || column = 11 || column = 48 || column = 49 ||
      column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else 0
private def row (mode : Fin 3) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, assignment mode⟩
private def data (mode : Fin 3) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [row mode]
    rom := UnifiedReduced.Setup.table (before mode)
    initial := (row mode).start
    terminal := (row mode).finish
    initialMemory := [⟨(Cell.register 0).addressCode, (0, 0), 0⟩,
      ⟨(Cell.register (register mode)).addressCode, (0, 0), Nat.pair 1 1⟩]
    terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
      ⟨(Cell.register (register mode)).addressCode, (6, 0), Nat.pair (low mode) (high mode)⟩] }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, [], [], []⟩
  program := []

private theorem core (mode : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment mode))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before mode))) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (fin_cases mode <;> decide +kernel)
    | (apply Verification.range16_contains; fin_cases mode <;> decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem timestamps (mode : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment mode)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases mode <;> decide +kernel

private theorem accepted (mode : Fin 3) : UnifiedReduced.Caller.MixedMemoryAccepted (data mode) [entry mode] := by
  constructor
  · constructor
    · intro current member
      have same : current = row mode := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append (core mode) (timestamps mode)
    · intro current member
      have same : current = row mode := List.mem_singleton.mp member
      subst current
      fin_cases mode <;> decide +kernel
    · exact List.Perm.swap _ _ []
    · intro current member
      have empty : (data mode).callers = [] := by fin_cases mode <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (data mode).calls = [] := by fin_cases mode <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same : current = row mode := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, (row mode).decoderQuery = ([entry mode].get i).query
    refine ⟨0, ?_⟩
    fin_cases mode <;> decide +kernel
  · fin_cases mode <;> decide +kernel

private theorem initialized (mode : Fin 3) : initialImage (before mode) (cells mode) = some (data mode).machine.initialMemory := by
  have control : (Cell.register (register mode)).read (before mode) = .ok 65537 (before mode) := by
    apply rX_register_frame (before := initialState) (after := before mode) rfl (register mode)
    fin_cases mode <;> apply read_register
    all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read (before mode) = .ok 0 (before mode) := by
    with_unfolding_all rfl
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  fin_cases mode <;> rfl

private theorem program_image (mode : Fin 3) : UnifiedReduced.Mixed.programImage (before mode) [0] = some [entry mode] := by
  have bytes : (Cell.ram 0).read (before mode) = .ok (bits mode) (before mode) := written_word_read initialState 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards (bits mode)) (before mode) =
      .ok ((literal mode).instruction (register mode)) (before mode) := by
    fin_cases mode <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields ((literal mode).instruction (register mode)) = some (entry mode).data := by
    fin_cases mode <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem inputs (mode : Fin 3) : UnifiedReduced.Caller.MixedMemoryInputs (data mode) [entry mode] (before mode) [] [0] (cells mode) := by
  refine ⟨⟨rfl, ?_, ?_⟩, program_image mode, initialized mode, ?_, ?_, rfl, rfl, ?_⟩
  · constructor <;> fin_cases mode <;> decide +kernel
  · fin_cases mode <;> decide +kernel
  · fin_cases mode <;> decide +kernel
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem preparation (mode : Fin 3) :
    UnifiedReduced.Caller.ControlPreparation (data mode) [entry mode] 8 (register mode) (literal mode) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply UnifiedReduced.Caller.PreparationProgram.uniform
    intro current member
    have same : current = entry mode := List.mem_singleton.mp member
    subst current
    rfl
  · fin_cases mode <;> decide +kernel
  · fin_cases mode <;> decide +kernel
  · fin_cases mode <;> decide +kernel

private theorem prepared (mode : Fin 3) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (data mode) (before mode) (cells mode) 8 (register mode) (literal mode) :=
  UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (accepted mode) (inputs mode) (preparation mode) (by fin_cases mode <;> decide) (by decide)

theorem literal_prepares_actual_control (upper : Bool) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (data (if upper then 1 else 0)) (before (if upper then 1 else 0))
      (cells (if upper then 1 else 0)) 8 12 (literal (if upper then 1 else 0)) := by
  cases upper
  · exact prepared 0
  · exact prepared 1

theorem keccak_control_is_reset :
    UnifiedReduced.Caller.PreparedBoundaryExecution (data 2) (before 2) (cells 2) 8 10
      (UnifiedReduced.Caller.hashPreparation .keccak) := prepared 2

theorem initial_control_is_different (upper : Bool) :
    (Cell.register 12).read (before (if upper then 1 else 0)) = .ok 65537 (before (if upper then 1 else 0)) ∧
      (literal (if upper then 1 else 0)).value ≠ 65537 := by
  constructor
  · apply rX_register_frame (before := initialState) (after := before (if upper then 1 else 0)) rfl 12
    apply read_register
    simp [initialState, Std.ExtDHashMap.get?_insert]
  · cases upper <;> decide +kernel

theorem keccak_initial_control_is_different :
    (Cell.register 10).read (before 2) = .ok 65537 (before 2) ∧
      (UnifiedReduced.Caller.hashPreparation .keccak).value ≠ 65537 := by
  constructor
  · apply rX_register_frame (before := initialState) (after := before 2) rfl 10
    apply read_register
    simp [initialState]
  · decide +kernel

theorem wrong_preparation_instruction_rejected :
    ¬ UnifiedReduced.Caller.ControlPreparation (data 0) [entry 0] 8 12 (.addi 0) := by
  intro scope
  have mismatch : (entry 0).instruction = UnifiedReduced.Caller.ControlLiteral.instruction (.addi 0) 12 := by
    cases scope.program with
    | uniform entries => exact entries (entry 0) (List.mem_singleton_self _)
    | straight _ atCut => exact atCut (entry 0) (List.mem_singleton_self _) (by decide +kernel)
    | arithmetic _ atCut => exact atCut (entry 0) (List.mem_singleton_self _) (by decide +kernel)
    | sequential _ atCut => exact atCut (entry 0) (List.mem_singleton_self _) (by decide +kernel)
    | wrappedSequential _ _ _ _ atCut => exact atCut (entry 0) (List.mem_singleton_self _) (by decide +kernel)
  simp [entry, literal, register, UnifiedReduced.Caller.hashPreparation,
    UnifiedReduced.Caller.ControlLiteral.instruction] at mismatch

theorem incomplete_prepared_g_span_rejected :
    ¬ UnifiedReduced.Caller.PreparedHashWindowInputs (data 0) (before 0) [] [0] (cells 0) [entry 0]
      (.blakeG true) 8 8 := by
  intro inputs
  have count := inputs.calls
  change 0 = 56 at count
  contradiction

theorem incomplete_prepared_keccak_span_rejected :
    ¬ UnifiedReduced.Caller.PreparedHashWindowInputs (data 2) (before 2) [] [0] (cells 2) [entry 2]
      .keccak 8 8 := by
  intro inputs
  have count := inputs.calls
  change 0 = 649 at count
  contradiction

private theorem round_inputs :
    UnifiedReduced.Caller.PreparedRoundInputs (data 1) (before 1) [] [0] (cells 1) [entry 1] 0 8 := by
  have context := inputs 1
  refine ⟨context.publicProgram, context.ordinaryProgram, context.initialization, context.distinct,
    context.aligned, context.setup, context.tables, ?_, preparation 1, by decide, ?_, ?_⟩
  · intro row member
    cases member
  · decide +kernel
  · decide +kernel

theorem round_literal_token_before_transport :
    ∃ tokens : List (MemoryToken babyBearModulus),
      ((data 1).machine.initialMemory ++ ((data 1).prefixSteps 8).map Prod.snd).Perm
        (tokens ++ ((data 1).prefixSteps 8).map Prod.fst) ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = ⟨0, 8⟩ := by
  have accepted := accepted 1
  have context := round_inputs
  have requests := UnifiedReduced.Caller.Proofs.request_binding (by decide +kernel) (by decide +kernel)
    accepted.toRequestChecks context.publicProgram
  have facts := UnifiedReduced.Caller.Proofs.mixed_memory_facts (by decide +kernel) (by decide +kernel)
    accepted context.publicProgram context.initialization requests
  obtain ⟨tokens, earlier, _⟩ := Proofs.Transfer.split_at facts 7
  have prefixEqual : Proofs.Transfer.beforeSteps (UnifiedReduced.Caller.Proofs.mixedData (data 1)) 7 =
      (data 1).prefixSteps 8 := by
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have matching := earlier.matching
  rw [prefixEqual] at matching
  refine ⟨tokens, matching, ?_⟩
  exact UnifiedReduced.Caller.Proofs.preparation_token (by decide +kernel) (by decide +kernel) accepted
    context.publicProgram context.ordinaryProgram context.initialization context.preparation (by decide) (by decide) matching

theorem round_memory_inputs_without_masks :
    UnifiedReduced.Caller.MixedMemoryInputs (data 1) [entry 1] (before 1) [] [0] (cells 1) :=
  UnifiedReduced.Caller.Proofs.prepared_round_memory_inputs (by decide +kernel) (by decide +kernel)
    (accepted 1) round_inputs (by decide)

theorem mismatched_round_preparation_flags_rejected :
    ¬ UnifiedReduced.Caller.PreparedRoundInputs (data 1) (before 1) [] [0] (cells 1) [entry 1] 1 8 := by
  intro context
  have instruction : (entry 1).instruction =
      (UnifiedReduced.Caller.hashPreparation (.blakeRound 1)).instruction 12 := by
    cases context.preparation.program with
    | uniform entries => exact entries (entry 1) (List.mem_singleton_self _)
    | straight _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | arithmetic _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | sequential _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | wrappedSequential _ _ _ _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
  change SailRV32.instruction.UTYPE (128, .Regidx 12, .LUI) =
    SailRV32.instruction.UTYPE (144, .Regidx 12, .LUI) at instruction
  cases instruction

theorem incomplete_prepared_round_span_rejected :
    ¬ UnifiedReduced.Caller.PreparedRoundWindowInputs (data 1) (before 1) [] [0] (cells 1) [entry 1] 0 8 8 := by
  intro context
  have count := context.calls
  change 0 = 10 at count
  contradiction

theorem prepared_round_two_bits_rejected [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {flags : Fin 8} {lower : Nat}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.PreparedRoundInputs trace initial ca oa domain program flags lower)
    (aligned : lower % 4 = 0) {worker : Delegation.Row p} (member : worker ∈ trace.workers.rows)
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  obtain ⟨round, mask⟩ := UnifiedReduced.Caller.prepared_round_masks_soundness hp clockInverse accepted context aligned worker member
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases same : first = round
  · have other : last ≠ round := by omega
    have zero := mask last
    rw [if_neg other, lastBit] at zero
    exact one_ne_zero zero
  · have zero := mask first
    rw [if_neg same, firstBit] at zero
    exact one_ne_zero zero

private def chainedBefore : State := wordWriteState (before 0) 4 0x00000613
private def chainedEntry : UnifiedReduced.ProgramEntry :=
  ⟨4, 0x00000613, UnifiedReduced.Caller.ControlLiteral.instruction (.addi 0) 12,
    ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private def chainedAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then 4
  else if column = 2 || column = 30 || column = 40 then 8
  else if column = 32 then 12
  else if column = 34 then 5
  else if column = 46 then 6
  else if column = 48 then 128
  else if column = 7 || column = 44 then 12
  else if column = 4 || column = 11 || column = 129 || column = 130 ||
      column = 131 || column = 132 || column = 133 then 1
  else 0
private def chainedRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, chainedAssignment⟩
private def chainedProgram : List UnifiedReduced.ProgramEntry := [entry 0, chainedEntry]
private def chainedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := { (data 0).machine with
    rows := [chainedRow, row 0]
    rom := UnifiedReduced.Setup.table chainedBefore
    terminal := chainedRow.finish
    terminalMemory := [⟨(Cell.register 0).addressCode, (9, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (10, 0), 0⟩] }
  workers := (data 0).workers
  program := []

private theorem chainedCore (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (if second then chainedAssignment else assignment 0))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table chainedBefore)) := by
  cases second
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, chainedAssignment, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem chainedTimestamps : FlatOperation.ConstraintsHoldFlat
    (Verification.environment chainedAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem chainedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted chainedData chainedProgram := by
  constructor
  · constructor
    · intro current member
      have rows : current = chainedRow ∨ current = row 0 := by simpa [chainedData] using member
      rcases rows with rfl | rfl
      · exact Verification.holds_append (chainedCore true) chainedTimestamps
      · exact Verification.holds_append (chainedCore false) (timestamps 0)
    · intro current member
      have rows : current = chainedRow ∨ current = row 0 := by simpa [chainedData] using member
      rcases rows with rfl | rfl <;> decide +kernel
    · change [((row 0).start), chainedRow.finish, (row 0).finish].Perm
        [chainedRow.finish, chainedRow.start, (row 0).start]
      have same : (row 0).finish = chainedRow.start := rfl
      rw [same]
      exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
    · intro current member
      have empty : chainedData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : chainedData.calls = [] := by decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = chainedRow ∨ current = row 0 := by simpa [chainedData] using member
    rcases rows with rfl | rfl
    · change ∃ i : Fin 2, chainedRow.decoderQuery = (chainedProgram.get i).query
      exact ⟨1, by decide +kernel⟩
    · change ∃ i : Fin 2, (row 0).decoderQuery = (chainedProgram.get i).query
      exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem chainedImage : UnifiedReduced.Mixed.programImage chainedBefore [0, 4] = some chainedProgram := by
  have first : (Cell.ram 0).read chainedBefore = .ok (bits 0) chainedBefore :=
    written_word_disjoint 4 0x00000613 (by decide) (written_word_read initialState 0 (bits 0))
  have second : (Cell.ram 4).read chainedBefore = .ok 0x00000613 chainedBefore :=
    written_word_read (before 0) 4 0x00000613
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (bits 0)) chainedBefore =
      .ok ((literal 0).instruction 12) chainedBefore := by with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards 0x00000613) chainedBefore =
      .ok (UnifiedReduced.Caller.ControlLiteral.instruction (.addi 0) 12) chainedBefore := by with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields ((literal 0).instruction 12) = some (entry 0).data := by
    with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (UnifiedReduced.Caller.ControlLiteral.instruction (.addi 0) 12) =
      some chainedEntry.data := by with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, decodeFirst, decodeSecond, fieldsFirst, fieldsSecond, bind, Option.bind, pure]
  rfl

private theorem chainedInputs :
    UnifiedReduced.Caller.MixedMemoryInputs chainedData chainedProgram chainedBefore [] [0, 4] (cells 0) := by
  refine ⟨⟨rfl, ?_, by decide +kernel⟩, chainedImage, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read chainedBefore = .ok 0 chainedBefore := by with_unfolding_all rfl
    have control : (Cell.register 12).read chainedBefore = .ok 65537 chainedBefore := by
      apply rX_register_frame (before := initialState) (after := chainedBefore) rfl 12
      apply read_register
      simp [initialState, Std.ExtDHashMap.get?_insert]
    change initialImage chainedBefore [.register 0, .register 12] = some chainedData.machine.initialMemory
    simp only [initialImage, zero, control, List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 12 := by simpa [cells, register] using member
    rcases choices with rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem chainedScope (second : Bool) : UnifiedReduced.Caller.ControlPreparation chainedData chainedProgram
    (if second then 12 else 8) 12 (if second then .addi 0 else .addi 128) := by
  refine ⟨.straight ?_ ?_, ?_, ?_, ?_⟩
  · intro current member
    have entries : current = entry 0 ∨ current = chainedEntry := by simpa [chainedProgram] using member
    rcases entries with rfl | rfl
    · exact ⟨12, .addi 128, by decide, rfl⟩
    · exact ⟨12, .addi 0, by decide, rfl⟩
  · intro current member address
    have entries : current = entry 0 ∨ current = chainedEntry := by simpa [chainedProgram] using member
    rcases entries with rfl | rfl
    · cases second
      · rfl
      · change 4 = 8 at address
        omega
    · cases second
      · change 8 = 4 at address
        omega
      · rfl
  · cases second <;> rfl
  · cases second <;> decide +kernel
  · cases second <;> decide +kernel

theorem distinct_literals_prepare_successive_cuts (second : Bool) :
    UnifiedReduced.Caller.PreparedBoundaryExecution chainedData chainedBefore (cells 0)
      (if second then 12 else 8) 12 (if second then .addi 0 else .addi 128) :=
  UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs (chainedScope second) (by decide) (by cases second <;> decide)

theorem successive_controls_share_one_history :
    UnifiedReduced.Caller.PreparedControlWindow chainedData chainedBefore (cells 0) 8 12 12 (.addi 128) 12 (.addi 0) :=
  UnifiedReduced.Caller.control_preparation_window_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs (chainedScope false) (chainedScope true) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem preparation_window_retains_all_prefix_steps :
    (chainedData.prefixSteps 8 ++ chainedData.windowSteps 8 12).Perm (chainedData.prefixSteps 12) :=
  UnifiedReduced.Caller.Proofs.prefix_window_partition (by decide +kernel) (by decide +kernel)
    chainedAccepted.toRequestChecks chainedInputs.publicProgram (by decide) (by decide) (by decide) (by decide)

theorem chained_preparation_uses_previous_write :
    (readToken chainedAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
      (readToken chainedAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 128 := by
  decide +kernel

theorem chained_wrong_literal_rejected :
    ¬ UnifiedReduced.Caller.ControlPreparation chainedData chainedProgram 12 12 (.addi 128) := by
  intro scope
  have encoding := UnifiedReduced.Caller.Proofs.preparation_instruction (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs.publicProgram chainedInputs.ordinaryProgram scope
    (row := chainedRow) (by simp [chainedData]) (by decide +kernel)
    (entry := chainedEntry) (by simp [chainedProgram]) (by decide +kernel)
  cases encoding

private def chainedFabricatedAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 48 then 0 else chainedAssignment column
private def chainedFabricatedData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainedData with machine := { chainedData.machine with
    rows := [⟨.machine, chainedFabricatedAssignment⟩, row 0] } }

theorem chained_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted chainedFabricatedData chainedProgram := by
  intro accepted
  let token := readToken chainedFabricatedAssignment UnifiedReduced.importedConstraintsMemoryPorts[2]
  have consumed : token ∈ chainedFabricatedData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ chainedFabricatedData.machine.initialMemory ++
      chainedFabricatedData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append_right _ consumed))

theorem native_chain_reaches_both_controls (gap : Bool) :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes chainedData chainedBefore (cells 0) 4 (if gap then 4 else 8) 8 12 ∧
      (Cell.register 12).read chain.atSecondStart = .ok 128 chain.atSecondStart ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish := by
  obtain ⟨chain, history⟩ := UnifiedReduced.Caller.mixed_window_chain_soundness
    (a := 4) (b := if gap then 4 else 8) (c := 8) (d := 12)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) chainedAccepted chainedInputs
    (by decide) (by cases gap <;> decide) (by decide) (by decide) (by decide)
    (by cases gap <;> decide) (by cases gap <;> decide) (by decide)
  have atStart := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs (chainedScope false) (by decide) (by decide)
    history.secondPrefixMatching history.secondStartBoundary
  have matching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 8) (upper := 12) chainedAccepted.toRequestChecks chainedInputs.publicProgram
    (by decide) (by decide) (by decide) (by decide)
    history.secondPrefixMatching history.secondMatching
  have atFinish := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs (chainedScope true) (by decide) (by decide) matching history.secondFinishBoundary
  exact ⟨chain, history, atStart.1, atFinish.1⟩

theorem empty_chain_gap_keeps_same_state {chain : UnifiedReduced.Caller.WindowChain babyBearModulus}
    (history : chain.Realizes chainedData chainedBefore (cells 0) 4 8 8 12) :
    chain.atFirstFinish = chain.atSecondStart := by
  have empty : chainedData.windowSteps 8 8 = [] := rfl
  have events : chain.gapEvents = [] := List.Perm.eq_nil (by simpa only [empty, List.map_nil] using history.gapPerm)
  have actual := history.gapHistory
  rw [events] at actual
  have nilState {before after : State} (h : SailHistory (cells 0) [] before after) : before = after := by
    cases h
    rfl
  exact nilState actual

theorem fabricated_chain_gap_state_rejected :
    ¬ ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes chainedData chainedBefore (cells 0) 4 8 8 12 ∧
      chain.atFirstFinish ≠ chain.atSecondStart := by
  rintro ⟨chain, history, different⟩
  exact different (empty_chain_gap_keeps_same_state history)

theorem native_sequence_reaches_successive_controls (gap : Bool) :
    ∃ (sequence : UnifiedReduced.Caller.WindowSequence babyBearModulus)
      (first middle last : UnifiedReduced.Caller.WindowSegment babyBearModulus),
      sequence.Realizes chainedData chainedBefore (cells 0) 4 [(4, if gap then 4 else 8), (8, 8), (8, 12)] ∧
      sequence.segments = [first, middle, last] ∧
      (Cell.register 12).read last.atStart = .ok 128 last.atStart ∧
      (Cell.register 12).read last.atFinish = .ok 0 last.atFinish := by
  obtain ⟨sequence, history⟩ := UnifiedReduced.Caller.mixed_window_sequence_soundness
    (cut := 4) (windows := [(4, if gap then 4 else 8), (8, 8), (8, 12)])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) chainedAccepted chainedInputs
    (by decide) (by decide) (by cases gap <;> simp [UnifiedReduced.Caller.WindowsOrdered])
  have segments := history.segments
  rcases shape : sequence.segments with _ | ⟨first, _ | ⟨middle, _ | ⟨last, tail⟩⟩⟩
  all_goals simp only [shape, UnifiedReduced.Caller.WindowSegmentsRealize] at segments
  · exact False.elim segments.2.2.2.2.2.2.2.2.2
  · exact False.elim segments.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · obtain ⟨_, _, _, prefixMatching, _, _, matching, startBoundary, finishBoundary, remaining⟩ :=
      segments.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have empty : tail = [] := by
      cases tail with
      | nil => rfl
      | cons _ _ => exact False.elim remaining
    subst tail
    have atStart := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
      chainedAccepted chainedInputs (chainedScope false) (by decide) (by decide) prefixMatching startBoundary
    have finalMatching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
      (lower := 8) (upper := 12) chainedAccepted.toRequestChecks chainedInputs.publicProgram
      (by decide) (by decide) (by decide) (by decide) prefixMatching matching
    have atFinish := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
      chainedAccepted chainedInputs (chainedScope true) (by decide) (by decide) finalMatching finishBoundary
    exact ⟨sequence, first, middle, last, history, shape, atStart.1, atFinish.1⟩

theorem empty_native_sequence_retains_initialized_prefix :
    UnifiedReduced.Caller.MixedWindowSequenceExecution chainedData chainedBefore (cells 0) 8 [] :=
  UnifiedReduced.Caller.mixed_window_sequence_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    chainedAccepted chainedInputs (by decide) (by decide) trivial

theorem overlapping_or_unaligned_sequences_rejected :
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 12), (8, 12)] ∧
    ¬ UnifiedReduced.Caller.WindowsOrdered 4 [(4, 6), (8, 12)] := by
  simp [UnifiedReduced.Caller.WindowsOrdered]

private theorem protocol_inputs :
    UnifiedReduced.Caller.PreparedProtocolInputs (data 1) (before 1) [] [0] (cells 1) [entry 1] [] := by
  have context := inputs 1
  refine ⟨⟨context.publicProgram, context.ordinaryProgram, context.initialization, context.distinct,
    context.aligned, context.setup, context.tables⟩, ?_, ?_⟩
  · intro region member
    cases member
  · intro row member
    cases member

private theorem program_round_region_scope :
    UnifiedReduced.Caller.ProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ := by
  refine ⟨⟨?_, ?_⟩, preparation 1, by decide, by decide, by decide +kernel⟩
  · intro current _ range
    dsimp only at range
    omega
  · intro current member
    cases member

private theorem sequential_round_preparation : UnifiedReduced.Caller.SequentialProgram [entry 1] := by
  intro current member
  have same : current = entry 1 := List.mem_singleton.mp member
  subst current
  exact .arithmetic (.lui 128 12)

theorem program_round_region_retains_empty_prepared_cut :
    UnifiedReduced.Caller.RoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ :=
  UnifiedReduced.Caller.program_round_region_soundness (by decide +kernel) (by decide +kernel)
    (accepted 1) (inputs 1).publicProgram (inputs 1).ordinaryProgram sequential_round_preparation
    program_round_region_scope

theorem wrapped_program_round_region_retains_empty_prepared_cut :
    UnifiedReduced.Caller.RoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ := by
  have registry : UnifiedReduced.Caller.WrappedSequentialProgram [entry 1] := by
    refine ⟨fun current member => .sequential (sequential_round_preparation current member), ?_⟩
    intro current member
    have same : current = entry 1 := List.mem_singleton.mp member
    subst current
    decide +kernel
  have scope : UnifiedReduced.Caller.WrappedProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ := by
    refine ⟨⟨?_, ?_⟩, preparation 1, by decide, by decide, by decide +kernel⟩
    · intro current member clock lower upper
      dsimp only at lower upper
      omega
    · intro current member; cases member
  exact UnifiedReduced.Caller.wrapped_program_round_region_soundness (by decide +kernel) (by decide +kernel)
    (inputs 1).setup (accepted 1) (inputs 1).publicProgram (inputs 1).ordinaryProgram registry scope

theorem wrapped_public_round_empty_cut_has_exact_coverage :
    UnifiedReduced.Caller.RoundWorkerCoverage (data 1) [⟨0, 8, 8⟩] := by
  have registry : UnifiedReduced.Caller.WrappedSequentialProgram [entry 1] := by
    refine ⟨fun current member => .sequential (sequential_round_preparation current member), ?_⟩
    intro current member
    have same : current = entry 1 := List.mem_singleton.mp member
    subst current
    decide +kernel
  have scope : UnifiedReduced.Caller.WrappedProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ := by
    refine ⟨⟨?_, ?_⟩, preparation 1, by decide, by decide, by decide +kernel⟩
    · intro current member clock lower upper
      dsimp only at lower upper
      omega
    · intro current member; cases member
  apply UnifiedReduced.Caller.wrapped_program_round_coverage_soundness (by decide +kernel) (by decide +kernel)
    (inputs 1).setup (accepted 1) (inputs 1).publicProgram (inputs 1).ordinaryProgram registry
  · intro region member
    have same : region = ⟨0, 8, 8⟩ := List.mem_singleton.mp member
    subst region
    exact scope
  · intro current member; cases member

private theorem round_region_scope :
    UnifiedReduced.Caller.RoundRegionInputs (data 1) [entry 1] ⟨0, 8, 8⟩ :=
  program_round_region_retains_empty_prepared_cut

theorem program_round_context_derives_local_shape :
    UnifiedReduced.Caller.PreparedProtocolInputs (data 1) (before 1) [] [0] (cells 1) [entry 1] [⟨0, 8, 8⟩] := by
  have context : UnifiedReduced.Caller.ProgramPreparedProtocolInputs
      (data 1) (before 1) [] [0] (cells 1) [entry 1] [⟨0, 8, 8⟩] := by
    refine ⟨protocol_inputs.toProtocolContextInputs, sequential_round_preparation, ?_, ?_⟩
    · intro region member
      have same : region = ⟨0, 8, 8⟩ := List.mem_singleton.mp member
      subst region
      exact program_round_region_scope
    · intro row member
      cases member
  exact UnifiedReduced.Caller.Proofs.program_prepared_protocol_inputs (by decide +kernel) (by decide +kernel)
    (accepted 1) context

theorem public_round_empty_cut_has_exact_coverage :
    UnifiedReduced.Caller.RoundWorkerCoverage (data 1) [⟨0, 8, 8⟩] := by
  have context := inputs 1
  apply UnifiedReduced.Caller.program_round_coverage_soundness (by decide +kernel) (by decide +kernel)
    (accepted 1) context.publicProgram context.ordinaryProgram sequential_round_preparation
  · intro region member
    have same : region = ⟨0, 8, 8⟩ := List.mem_singleton.mp member
    subst region
    exact program_round_region_scope
  · intro entry member
    cases member

theorem round_region_seed_retains_preparation_timestamp :
    ∃ start finish : List (MemoryToken babyBearModulus),
      ((data 1).machine.initialMemory ++ ((data 1).prefixSteps 8).map Prod.snd).Perm
        (start ++ ((data 1).prefixSteps 8).map Prod.fst) ∧
      (start ++ ((data 1).windowSteps 8 8).map Prod.snd).Perm
        (finish ++ ((data 1).windowSteps 8 8).map Prod.fst) ∧
      ∃ token ∈ start, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = ⟨0, 8⟩ := by
  have requests := UnifiedReduced.Caller.Proofs.request_binding (by decide +kernel) (by decide +kernel)
    (accepted 1).toRequestChecks protocol_inputs.publicProgram
  have facts := UnifiedReduced.Caller.Proofs.mixed_memory_facts (by decide +kernel) (by decide +kernel)
    (accepted 1) protocol_inputs.publicProgram protocol_inputs.initialization requests
  obtain ⟨start, prefixFacts, suffix⟩ := Proofs.Transfer.split_at facts 7
  obtain ⟨finish, window, _⟩ := Proofs.Transfer.split_at suffix 7
  have prefixMatching := prefixFacts.matching
  rw [UnifiedReduced.Caller.Proofs.mixed_prefix_steps (data 1) (cut := 8) (by decide)] at prefixMatching
  change Proofs.Transfer.Facts ⟨start, finish,
    Proofs.Transfer.windowSteps (UnifiedReduced.Caller.Proofs.mixedData (data 1)) 7 7⟩ at window
  rw [← UnifiedReduced.Caller.Proofs.mixed_window_steps (by decide +kernel) (by decide +kernel)
    (lower := 8) (upper := 8) (accepted 1).toRequestChecks protocol_inputs.publicProgram
    (by decide) (by decide) (by decide) (by decide)] at window
  exact ⟨start, finish, prefixMatching, window.matching,
    UnifiedReduced.Caller.Proofs.preparation_token (by decide +kernel) (by decide +kernel) (accepted 1)
      protocol_inputs.publicProgram protocol_inputs.ordinaryProgram protocol_inputs.initialization
      round_region_scope.preparation (by decide) (by decide) prefixMatching⟩

theorem round_region_wrong_flags_rejected :
    ¬ UnifiedReduced.Caller.RoundRegionInputs (data 1) [entry 1] ⟨1, 8, 8⟩ := by
  intro scope
  have instruction : (entry 1).instruction =
      (UnifiedReduced.Caller.hashPreparation (.blakeRound 1)).instruction 12 := by
    cases scope.preparation.program with
    | uniform entries => exact entries (entry 1) (List.mem_singleton_self _)
    | straight _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | arithmetic _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | sequential _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
    | wrappedSequential _ _ _ _ atCut => exact atCut (entry 1) (List.mem_singleton_self _) (by decide +kernel)
  change SailRV32.instruction.UTYPE (128, .Regidx 12, .LUI) =
    SailRV32.instruction.UTYPE (144, .Regidx 12, .LUI) at instruction
  cases instruction

theorem program_round_wrong_flags_rejected :
    ¬ UnifiedReduced.Caller.ProgramRoundRegionInputs (data 1) [entry 1] ⟨1, 8, 8⟩ := by
  intro scope
  exact round_region_wrong_flags_rejected
    (UnifiedReduced.Caller.program_round_region_soundness (by decide +kernel) (by decide +kernel)
      (accepted 1) (inputs 1).publicProgram (inputs 1).ordinaryProgram sequential_round_preparation scope)

theorem program_round_bad_cuts_rejected :
    (¬ UnifiedReduced.Caller.ProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 8, 52⟩) ∧
    (¬ UnifiedReduced.Caller.ProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 12, 8⟩) ∧
    (¬ UnifiedReduced.Caller.ProgramRoundRegionInputs (data 1) [entry 1] ⟨0, 8, 10⟩) := by
  refine ⟨fun scope => ?_, fun scope => ?_, fun scope => ?_⟩
  · have extent := scope.extent.2
    norm_num at extent
  · have extent := scope.extent.1
    norm_num at extent
  · have aligned := scope.aligned.2
    norm_num at aligned

theorem prepared_round_region_two_bits_rejected [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List UnifiedReduced.Caller.RoundRegion}
    {region : UnifiedReduced.Caller.RoundRegion}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.PreparedProtocolInputs trace initial ca oa domain program regions)
    (scope : UnifiedReduced.Caller.RoundRegionInputs trace program region)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.windowRows region.lower region.upper)
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  obtain ⟨round, mask⟩ := UnifiedReduced.Caller.prepared_round_region_masks_soundness hp clockInverse accepted context scope worker member
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases same : first = round
  · have other : last ≠ round := by omega
    have zero := mask last
    rw [if_neg other, lastBit] at zero
    exact one_ne_zero zero
  · have zero := mask first
    rw [if_neg same, firstBit] at zero
    exact one_ne_zero zero

theorem program_round_region_two_bits_rejected [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List UnifiedReduced.Caller.RoundRegion}
    {region : UnifiedReduced.Caller.RoundRegion}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.ProgramPreparedProtocolInputs trace initial ca oa domain program regions)
    (included : region ∈ regions)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.windowRows region.lower region.upper)
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  have inputs := UnifiedReduced.Caller.Proofs.program_prepared_protocol_inputs
    (by norm_num [timestampBase]; omega) clockInverse accepted context
  exact prepared_round_region_two_bits_rejected hp clockInverse accepted inputs
    (inputs.scopes region included) member different firstBit lastBit

theorem public_round_live_masks_reject_two_bits [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List UnifiedReduced.Caller.RoundRegion}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.ProtocolContextInputs trace initial ca oa domain program)
    (registry : UnifiedReduced.Caller.SequentialProgram program)
    (scopes : ∀ region ∈ regions, UnifiedReduced.Caller.ProgramRoundRegionInputs trace program region)
    (coverage : UnifiedReduced.Caller.ProgramRoundCallerCoverage trace regions)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.rows) (family : worker.family = .blakeRound)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker))
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  obtain ⟨round, mask⟩ := UnifiedReduced.Caller.program_round_live_masks_soundness hp clockInverse
    accepted context registry scopes coverage worker member family live
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases same : first = round
  · have other : last ≠ round := by omega
    have zero := mask last
    rw [if_neg other, lastBit] at zero
    exact one_ne_zero zero
  · have zero := mask first
    rw [if_neg same, firstBit] at zero
    exact one_ne_zero zero

theorem wrapped_public_round_live_masks_reject_two_bits [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry} {regions : List UnifiedReduced.Caller.RoundRegion}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.ProtocolContextInputs trace initial ca oa domain program)
    (registry : UnifiedReduced.Caller.WrappedSequentialProgram program)
    (scopes : ∀ region ∈ regions, UnifiedReduced.Caller.WrappedProgramRoundRegionInputs trace program region)
    (coverage : UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage trace regions)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.rows) (family : worker.family = .blakeRound)
    (live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker))
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  obtain ⟨round, mask⟩ := UnifiedReduced.Caller.wrapped_program_round_live_masks_soundness hp clockInverse
    accepted context registry scopes coverage worker member family live
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases same : first = round
  · have other : last ≠ round := by omega
    have zero := mask last
    rw [if_neg other, lastBit] at zero
    exact one_ne_zero zero
  · have zero := mask first
    rw [if_neg same, firstBit] at zero
    exact one_ne_zero zero

private def sequentialBefore (custom : Bool) : State := wordWriteState (wordWriteState initialState 0 (if custom then 0xc2c64673 else 0x00c60633)) 4 0x00000613
private def sequentialEntry (custom : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, (if custom then 0xc2c64673 else 0x00c60633), (if custom then .ZIMOP_MOP_RR (4, .Regidx 12, .Regidx 12, .Regidx 12) else .RTYPE (.Regidx 12, .Regidx 12, .Regidx 12, .ADD)),
    ⟨.machine, 12, 12, 12, ⟨0, 0⟩, (if custom then 512 else 1), 0⟩⟩
private def sequentialProgram (custom : Bool) : List UnifiedReduced.ProgramEntry := [(sequentialEntry custom), chainedEntry]
private def sequentialAssignment (custom : Bool) (second : Bool) (column : Nat) : ZMod babyBearModulus :=
  if second then
    if column = 34 then 0 else if column = 48 || column = 49 then (if custom then 3 else 2) else chainedAssignment column
  else
    if custom && column = 11 then 0 else if custom && column = 20 then 1
    else if column = 5 || column = 6 || column = 7 || column = 38 || column = 44 then 12
    else if column = 50 || column = 51 then (if custom then 3 else 2)
    else if column = 46 then 5
    else if column = 80 then 65537 * 65537 * 943718400
    else if column = 36 || column = 37 || column = 42 || column = 43 || column = 48 || column = 49 then 1
    else if column = 8 then 0 else assignment 0 column
private def sequentialRow (custom : Bool) (second : Bool) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, sequentialAssignment custom second⟩
private def sequentialData (custom : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainedData with machine := { chainedData.machine with
    rows := [sequentialRow custom true, sequentialRow custom false]
    rom := UnifiedReduced.Setup.table (sequentialBefore custom) } }

private theorem sequentialCore (custom : Bool) (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (sequentialAssignment custom second))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (sequentialBefore custom))) := by
  cases custom <;> cases second
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignment, chainedAssignment, sequentialAssignment,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem sequentialTimestamps (custom : Bool) (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (sequentialAssignment custom second)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases custom <;> cases second <;> decide +kernel

private theorem sequentialAccepted (custom : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (sequentialData custom) (sequentialProgram custom) := by
  constructor
  · constructor
    · intro current member
      have rows : current = sequentialRow custom true ∨ current = sequentialRow custom false := by simpa [sequentialData] using member
      rcases rows with rfl | rfl
      · exact Verification.holds_append (sequentialCore custom true) (sequentialTimestamps custom true)
      · exact Verification.holds_append (sequentialCore custom false) (sequentialTimestamps custom false)
    · intro current member
      have rows : current = sequentialRow custom true ∨ current = sequentialRow custom false := by simpa [sequentialData] using member
      rcases rows with rfl | rfl <;> cases custom <;> decide +kernel
    · have initial : (sequentialData custom).machine.initial = (sequentialRow custom false).start := by cases custom <;> rfl
      have terminal : (sequentialData custom).machine.terminal = (sequentialRow custom true).finish := by cases custom <;> rfl
      rw [initial, terminal]
      change [((sequentialRow custom false).start), (sequentialRow custom true).finish, (sequentialRow custom false).finish].Perm
        [(sequentialRow custom true).finish, (sequentialRow custom true).start, (sequentialRow custom false).start]
      have same : (sequentialRow custom false).finish = (sequentialRow custom true).start := by cases custom <;> rfl
      rw [same]
      exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
    · intro current member
      have empty : (sequentialData custom).callers = [] := by cases custom <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (sequentialData custom).calls = [] := by cases custom <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = sequentialRow custom true ∨ current = sequentialRow custom false := by simpa [sequentialData] using member
    rcases rows with rfl | rfl
    · change ∃ i : Fin 2, (sequentialRow custom true).decoderQuery = ((sequentialProgram custom).get i).query
      exact ⟨1, by cases custom <;> decide +kernel⟩
    · change ∃ i : Fin 2, (sequentialRow custom false).decoderQuery = ((sequentialProgram custom).get i).query
      exact ⟨0, by cases custom <;> decide +kernel⟩
  · cases custom <;> decide +kernel

private theorem sequentialImage (custom : Bool) : UnifiedReduced.Mixed.programImage (sequentialBefore custom) [0, 4] = some (sequentialProgram custom) := by
  have first : (Cell.ram 0).read (sequentialBefore custom) = .ok (if custom then 0xc2c64673 else 0x00c60633) (sequentialBefore custom) :=
    written_word_disjoint 4 0x00000613 (by decide) (written_word_read initialState 0 (if custom then 0xc2c64673 else 0x00c60633))
  have second : (Cell.ram 4).read (sequentialBefore custom) = .ok 0x00000613 (sequentialBefore custom) :=
    written_word_read (wordWriteState initialState 0 (if custom then 0xc2c64673 else 0x00c60633)) 4 0x00000613
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (if custom then 0xc2c64673 else 0x00c60633)) (sequentialBefore custom) =
      .ok (sequentialEntry custom).instruction (sequentialBefore custom) := by cases custom <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards 0x00000613) (sequentialBefore custom) =
      .ok chainedEntry.instruction (sequentialBefore custom) := by cases custom <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (sequentialEntry custom).instruction = some (sequentialEntry custom).data := by
    cases custom <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields chainedEntry.instruction = some chainedEntry.data := by
    cases custom <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, decodeFirst, decodeSecond, fieldsFirst, fieldsSecond, bind, Option.bind, pure]
  rfl

private theorem sequentialInputs (custom : Bool) :
    UnifiedReduced.Caller.MixedMemoryInputs (sequentialData custom) (sequentialProgram custom) (sequentialBefore custom) [] [0, 4] (cells 0) := by
  refine ⟨⟨rfl, ?_, by cases custom <;> decide +kernel⟩, sequentialImage custom, ?_, by cases custom <;> decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (sequentialBefore custom) = .ok 0 (sequentialBefore custom) := by cases custom <;> with_unfolding_all rfl
    have control : (Cell.register 12).read (sequentialBefore custom) = .ok 65537 (sequentialBefore custom) := by
      apply rX_register_frame (before := initialState) (after := sequentialBefore custom) rfl 12
      apply read_register
      simp [initialState, Std.ExtDHashMap.get?_insert]
    change initialImage (sequentialBefore custom) [.register 0, .register 12] = some (sequentialData custom).machine.initialMemory
    simp only [initialImage, zero, control, List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 12 := by simpa [cells, register] using member
    rcases choices with rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem sequentialScope (custom : Bool) : UnifiedReduced.Caller.ControlPreparation (sequentialData custom) (sequentialProgram custom) 12 12 (.addi 0) := by
  refine ⟨.sequential ?_ ?_, rfl, by cases custom <;> decide +kernel, by cases custom <;> decide +kernel⟩
  · intro current member
    have entries : current = (sequentialEntry custom) ∨ current = chainedEntry := by simpa [sequentialProgram] using member
    rcases entries with rfl | rfl
    · cases custom
      · exact .arithmetic (.add 12 12 12)
      · exact .triadd 12 12 12
    · exact .arithmetic (.addi 0 0 12)
  · intro current member address
    have entries : current = (sequentialEntry custom) ∨ current = chainedEntry := by simpa [sequentialProgram] using member
    rcases entries with rfl | rfl
    · change 4 = 8 at address
      omega
    · rfl

private theorem sequential_prefix_before_preparation (custom : Bool) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (sequentialData custom) (sequentialBefore custom) (cells 0) 12 12 (.addi 0) :=
  UnifiedReduced.Caller.control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (sequentialAccepted custom) (sequentialInputs custom) (sequentialScope custom) (by decide) (by decide)

private theorem sequential_preparation_uses_prior_aliased_add (custom : Bool) :
    (readToken (sequentialAssignment custom true) UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
    (readToken (sequentialAssignment custom true) UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = (if custom then 196611 else 131074) := by
  cases custom <;> decide +kernel

private theorem sequential_preparation_has_actual_control (custom : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (state : State), events.Perm (((sequentialData custom).prefixSteps 12).map transferEvent) ∧
      SailHistory (cells 0) events (sequentialBefore custom) state ∧ UnifiedReduced.Caller.NativeBoundary tokens state (cells 0) ∧
      (Cell.register 12).read state = .ok 0 state ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 10 ∧ token.word.toBitVec = 0 :=
  sequential_prefix_before_preparation custom

private def sequentialFabricatedData (custom : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { (sequentialData custom) with machine := { (sequentialData custom).machine with rows :=
    [⟨.machine, fun column => if column = 48 then 0 else sequentialAssignment custom true column⟩, sequentialRow custom false] } }

private theorem sequential_prefix_and_preparation_share_history (custom : Bool) :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes (sequentialData custom) (sequentialBefore custom) (cells 0) 4 8 8 12 ∧
      (Cell.register 12).read chain.atFirstFinish = .ok (if custom then 196611 else 131074) chain.atFirstFinish ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish := by
  obtain ⟨chain, history⟩ := UnifiedReduced.Caller.mixed_window_chain_soundness
    (a := 4) (b := 8) (c := 8) (d := 12)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (sequentialAccepted custom) (sequentialInputs custom)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have firstMatching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 4) (upper := 8) (sequentialAccepted custom).toRequestChecks (sequentialInputs custom).publicProgram
    (by decide) (by decide) (by decide) (by decide) history.firstPrefixMatching history.firstMatching
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (if custom then 3 else 2) (if custom then 3 else 2)⟩
  have produced : token ∈ (sequentialData custom).machine.initialMemory ++ ((sequentialData custom).prefixSteps 8).map Prod.snd := by cases custom <;> decide +kernel
  have notRead : token ∉ ((sequentialData custom).prefixSteps 8).map Prod.fst := by cases custom <;> decide +kernel
  have present : token ∈ chain.firstFinish := by
    rcases List.mem_append.mp (firstMatching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  obtain ⟨cell, _, address, firstRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read history.firstFinishBoundary present
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective address
  subst cell
  have finalMatching := UnifiedReduced.Caller.Proofs.matching_at_next_cut (by decide +kernel) (by decide +kernel)
    (lower := 8) (upper := 12) (sequentialAccepted custom).toRequestChecks (sequentialInputs custom).publicProgram
    (by decide) (by decide) (by decide) (by decide) history.secondPrefixMatching history.secondMatching
  have lastRead := UnifiedReduced.Caller.Proofs.preparation_at_boundary (by decide +kernel) (by decide +kernel)
    (sequentialAccepted custom) (sequentialInputs custom) (sequentialScope custom) (by decide) (by decide) finalMatching history.secondFinishBoundary
  have bits : token.word.toBitVec = ((if custom then 196611 else 131074) : BitVec 32) := by
    simp only [token, MemoryToken.word, Nat.unpair_pair]
    cases custom <;> rfl
  rw [bits] at firstRead
  exact ⟨chain, history, firstRead, lastRead.1⟩

private theorem sequential_preparation_fabricated_read_rejected (custom : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (sequentialFabricatedData custom) (sequentialProgram custom) := by
  intro accepted
  let token := readToken (fun column => if column = 48 then 0 else sequentialAssignment custom true column)
    UnifiedReduced.importedConstraintsMemoryPorts[2]
  have consumed : token ∈ (sequentialFabricatedData custom).mixedSteps.map Prod.fst := by cases custom <;> decide +kernel
  have absent : token ∉ (sequentialFabricatedData custom).machine.initialMemory ++ (sequentialFabricatedData custom).mixedSteps.map Prod.snd := by cases custom <;> decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append_right _ consumed))

theorem nonliteral_add_before_preparation :
    UnifiedReduced.Caller.PreparedBoundaryExecution (sequentialData false) (sequentialBefore false) (cells 0) 12 12 (.addi 0) :=
  sequential_prefix_before_preparation false

theorem arithmetic_preparation_uses_prior_aliased_add :
    (readToken ((sequentialAssignment false) true) UnifiedReduced.importedConstraintsMemoryPorts[2]).time = (6, 0) ∧
    (readToken ((sequentialAssignment false) true) UnifiedReduced.importedConstraintsMemoryPorts[2]).word.toBitVec = 131074 :=
  sequential_preparation_uses_prior_aliased_add false

theorem arithmetic_preparation_has_actual_control :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (state : State), events.Perm (((sequentialData false).prefixSteps 12).map transferEvent) ∧
      SailHistory (cells 0) events (sequentialBefore false) state ∧ UnifiedReduced.Caller.NativeBoundary tokens state (cells 0) ∧
      (Cell.register 12).read state = .ok 0 state ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 10 ∧ token.word.toBitVec = 0 :=
  sequential_preparation_has_actual_control false

theorem arithmetic_prefix_and_preparation_share_history :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes (sequentialData false) (sequentialBefore false) (cells 0) 4 8 8 12 ∧
      (Cell.register 12).read chain.atFirstFinish = .ok 131074 chain.atFirstFinish ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish :=
  sequential_prefix_and_preparation_share_history false

theorem arithmetic_preparation_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (sequentialFabricatedData false) (sequentialProgram false) :=
  sequential_preparation_fabricated_read_rejected false

theorem triadd_before_preparation :
    UnifiedReduced.Caller.PreparedBoundaryExecution (sequentialData true) (sequentialBefore true) (cells 0) 12 12 (.addi 0) :=
  sequential_prefix_before_preparation true

theorem triadd_prefix_and_preparation_share_history :
    ∃ chain : UnifiedReduced.Caller.WindowChain babyBearModulus,
      chain.Realizes (sequentialData true) (sequentialBefore true) (cells 0) 4 8 8 12 ∧
      (Cell.register 12).read chain.atFirstFinish = .ok 196611 chain.atFirstFinish ∧
      (Cell.register 12).read chain.atSecondFinish = .ok 0 chain.atSecondFinish :=
  sequential_prefix_and_preparation_share_history true

theorem triadd_preparation_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (sequentialFabricatedData true) (sequentialProgram true) :=
  sequential_preparation_fabricated_read_rejected true

theorem sequential_profile_excludes_jump (imm : BitVec 21) (rd : BitVec 5) :
    ¬ UnifiedReduced.Caller.SequentialInstruction (.JAL (imm, .Regidx rd)) := by
  intro supported
  cases supported with
  | arithmetic supported => cases supported

theorem sequential_profile_excludes_comparison (rs2 rs1 rd : BitVec 5) :
    ¬ UnifiedReduced.Caller.SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)) := by
  intro supported
  cases supported with
  | arithmetic supported => cases supported

/-- A publicly zero x12 seed leaves an unissued round worker outside every
    exclusive-mask ABI. This neither constructs nor excludes an accepted worker. -/
theorem unissued_round_zero_seed_has_no_mask [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca : List (BitVec 32)} {domain : List Cell}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (publicProgram : UnifiedReduced.Caller.RequestInputs trace initial ca)
    (image : initialImage initial domain = some trace.machine.initialMemory)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.rows) (family : worker.family = .blakeRound)
    (zero : (Delegation.Requests.fulfillment worker).time = (0, 0))
    (seed : (Cell.register 12).read initial = .ok 0 initial) :
    ¬ ∃ round, Blake2Round.Memory.RoundMask worker.assignment round := by
  obtain ⟨actual, read, masks⟩ := UnifiedReduced.Caller.unissued_round_control_soundness hp clockInverse
    accepted publicProgram image member family zero
  have same : actual = 0 := (EStateM.Result.ok.inj (read.symm.trans seed)).1
  subst actual
  rintro ⟨round, mask⟩
  obtain ⟨flags, encoded⟩ := (masks round).mp mask
  change 0 = flags.val + 8 * 2 ^ round.val at encoded
  have positive : 0 < 2 ^ round.val := pow_pos (by decide) _
  omega

private def pcRelativePC (wrap : Bool) : BitVec 32 := if wrap then 0x10004 else 4
private def pcRelativeImmediate (wrap : Bool) : BitVec 20 := if wrap then 0xfffff else 128
private def pcRelativeBits (wrap : Bool) : BitVec 32 := if wrap then 0xfffff617 else 0x00080617
private def pcRelativeValue (wrap : Bool) : BitVec 32 := if wrap then 61444 else 524292
private def pcRelativeEntry (wrap : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨pcRelativePC wrap, pcRelativeBits wrap, .UTYPE (pcRelativeImmediate wrap, .Regidx 12, .AUIPC),
    ⟨.machine, 0, 0, 12, Word.ofBitVec (pcRelativeImmediate wrap ++ (0 : BitVec 12)), 4, 0⟩⟩
private def pcRelativeBefore (wrap : Bool) : State := wordWriteState initialState (pcRelativePC wrap).toNat (pcRelativeBits wrap)
private def pcRelativeCells : List Cell := [.register 0, .register 12]
private def pcRelativeAssignment (wrap : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 0 || column = 2 || column = 40 then 4
  else if column = 1 || column = 31 || column = 52 then if wrap then 1 else 0
  else if column = 30 || column = 32 then 8
  else if column = 7 || column = 44 then 12
  else if column = 8 then if wrap then 61440 else 0
  else if column = 9 then if wrap then 65535 else 8
  else if column = 50 then if wrap then 61444 else 4
  else if column = 51 then if wrap then 0 else 8
  else if column = 4 || column = 13 || column = 48 || column = 49 ||
      column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else 0
private def pcRelativeRow (wrap : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, pcRelativeAssignment wrap⟩
private def pcRelativeData (wrap : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [pcRelativeRow wrap]
    rom := UnifiedReduced.Setup.table (pcRelativeBefore wrap)
    initial := (pcRelativeRow wrap).start
    terminal := (pcRelativeRow wrap).finish
    initialMemory := [⟨(Cell.register 0).addressCode, (0, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 1 1⟩]
    terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
      ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (Word.ofBitVec (pcRelativeValue wrap)).lo (Word.ofBitVec (pcRelativeValue wrap)).hi⟩] }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, [], [], []⟩
  program := []

private theorem pcRelativeCore (wrap : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (pcRelativeAssignment wrap))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (pcRelativeBefore wrap))) := by
  cases wrap <;> simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, pcRelativeAssignment, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem pcRelativeClocks (wrap : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (pcRelativeAssignment wrap)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases wrap <;> decide +kernel

private theorem pcRelativeAccepted (wrap : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (pcRelativeData wrap) [pcRelativeEntry wrap] := by
  constructor
  · constructor
    · intro current member
      have same : current = pcRelativeRow wrap := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append (pcRelativeCore wrap) (pcRelativeClocks wrap)
    · intro current member
      have same : current = pcRelativeRow wrap := List.mem_singleton.mp member
      subst current
      cases wrap <;> decide +kernel
    · exact List.Perm.swap _ _ []
    · intro _ member
      have empty : (pcRelativeData wrap).callers = [] := by cases wrap <;> decide +kernel
      rw [empty] at member
      cases member
    · intro _ member; cases member
    · intro _ member; cases member
    · have empty : (pcRelativeData wrap).calls = [] := by cases wrap <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same : current = pcRelativeRow wrap := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, (pcRelativeRow wrap).decoderQuery = ([pcRelativeEntry wrap].get i).query
    exact ⟨0, by cases wrap <;> decide +kernel⟩
  · cases wrap <;> decide +kernel

private theorem pcRelativeProgram (wrap : Bool) :
    UnifiedReduced.Mixed.programImage (pcRelativeBefore wrap) [pcRelativePC wrap] = some [pcRelativeEntry wrap] := by
  have bytes : (Cell.ram (pcRelativePC wrap)).read (pcRelativeBefore wrap) = .ok (pcRelativeBits wrap) (pcRelativeBefore wrap) := by
    cases wrap <;> exact written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards (pcRelativeBits wrap)) (pcRelativeBefore wrap) =
      .ok (pcRelativeEntry wrap).instruction (pcRelativeBefore wrap) := by cases wrap <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields (pcRelativeEntry wrap).instruction = some (pcRelativeEntry wrap).data := by
    cases wrap <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem pcRelativeImage (wrap : Bool) :
    initialImage (pcRelativeBefore wrap) pcRelativeCells = some (pcRelativeData wrap).machine.initialMemory := by
  have zero : (Cell.register 0).read (pcRelativeBefore wrap) = .ok 0 (pcRelativeBefore wrap) := rfl
  have control : (Cell.register 12).read (pcRelativeBefore wrap) = .ok 65537 (pcRelativeBefore wrap) := by
    apply read_register
    simp [pcRelativeBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, pcRelativeCells, List.mapM_cons, List.mapM_nil, zero, control, bind, Option.bind]
  rfl

private theorem pcRelativeInputs (wrap : Bool) :
    UnifiedReduced.Caller.MixedMemoryInputs (pcRelativeData wrap) [pcRelativeEntry wrap]
      (pcRelativeBefore wrap) [] [pcRelativePC wrap] pcRelativeCells := by
  refine ⟨⟨rfl, ?_, ?_⟩, pcRelativeProgram wrap, pcRelativeImage wrap, by decide, ?_, rfl, rfl, ?_⟩
  · cases wrap <;> change 4 < timestampBase ∧ 0 < timestampBase <;> norm_num [timestampBase]
  · cases wrap <;> decide +kernel
  · intro cell member
    simp [pcRelativeCells] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  · intro _ member; cases member

private theorem pcRelativeScope (wrap : Bool) :
    UnifiedReduced.Caller.PCRelativePreparation (pcRelativeData wrap) [pcRelativeEntry wrap] 8 12 (pcRelativeImmediate wrap) := by
  refine ⟨⟨?_, ?_⟩, ?_, rfl, ?_, ?_⟩
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact .sequential (.arithmetic (.auipc _ _))
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    cases wrap <;> decide +kernel
  · intro entry member _
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  · cases wrap <;> decide +kernel
  · cases wrap <;> decide +kernel

theorem auipc_preparation_execution (wrap : Bool) :
    UnifiedReduced.Caller.PCRelativePreparedBoundaryExecution (pcRelativeData wrap)
      (pcRelativeBefore wrap) pcRelativeCells 8 12 (pcRelativeImmediate wrap) :=
  UnifiedReduced.Caller.pc_relative_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pcRelativeAccepted wrap) (pcRelativeInputs wrap) (pcRelativeScope wrap) (by decide) (by decide)

/-- Nonzero public PCs contribute to the control; the AUIPC immediate alone is insufficient. -/
theorem auipc_preparation_uses_public_pc (wrap : Bool) :
    UnifiedReduced.Caller.pcRelativeControl (pcRelativeData wrap) 8 (pcRelativeImmediate wrap) ≠
      pcRelativeImmediate wrap ++ (0 : BitVec 12) := by cases wrap <;> decide +kernel

/-- Both an ordinary PC-relative value and a 32-bit wrapped sum reach the actual
    cut state. The original native write timestamp six is retained. -/
theorem auipc_prepared_states (wrap : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atCut : State),
      events.Perm (((pcRelativeData wrap).prefixSteps 8).map transferEvent) ∧
      SailHistory pcRelativeCells events (pcRelativeBefore wrap) atCut ∧
      UnifiedReduced.Caller.NativeBoundary tokens atCut pcRelativeCells ∧
      (Cell.register 12).read (pcRelativeBefore wrap) = .ok 65537 (pcRelativeBefore wrap) ∧
      (Cell.register 12).read atCut = .ok (pcRelativeValue wrap) atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = Word.ofBitVec (pcRelativeValue wrap) := by
  obtain ⟨tokens, events, atCut, permutation, history, boundary, read, token, member, address, time, word⟩ :=
    auipc_preparation_execution wrap
  have value : UnifiedReduced.Caller.pcRelativeControl (pcRelativeData wrap) 8 (pcRelativeImmediate wrap) = pcRelativeValue wrap := by
    cases wrap <;> decide +kernel
  have initial : (Cell.register 12).read (pcRelativeBefore wrap) = .ok 65537 (pcRelativeBefore wrap) := by
    apply read_register
    simp [pcRelativeBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  exact ⟨tokens, events, atCut, permutation, history, boundary, initial, value ▸ read,
    token, member, address, time, value ▸ word⟩

theorem auipc_wrong_immediate_rejected :
    ¬ UnifiedReduced.Caller.PCRelativePreparation (pcRelativeData false) [pcRelativeEntry false] 8 12 129 := by
  intro scope
  have instruction := scope.atCut (pcRelativeEntry false) (List.mem_singleton_self _) (by decide +kernel)
  have immediate := congrArg Prod.fst (SailRV32.instruction.UTYPE.inj instruction)
  change (128 : BitVec 20) = 129 at immediate
  exact (by decide : (128 : BitVec 20) ≠ 129) immediate

private def forgedPCRelativeData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { pcRelativeData false with machine := { (pcRelativeData false).machine with
      rows := [⟨.machine, fun column => if column = 48 then 2 else pcRelativeAssignment false column⟩] } }

theorem auipc_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedPCRelativeData [pcRelativeEntry false] := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 2 1⟩
  have member : token ∈ forgedPCRelativeData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedPCRelativeData.machine.initialMemory ++ forgedPCRelativeData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

private def hashAUIPCMode (keccak : Bool) : Fin 3 := if keccak then 2 else 0
private def hashAUIPCSpan (keccak : Bool) : Delegation.Caller.HashSpan := if keccak then .keccak else .blakeG true
private def hashAUIPCPC (keccak : Bool) : BitVec 32 := if keccak then 4096 else 128
private def hashAUIPCImmediate (keccak : Bool) : BitVec 20 := if keccak then 0xfffff else 0
private def hashAUIPCBits (keccak : Bool) : BitVec 32 := if keccak then 0xfffff517 else 0x00000617
private def hashAUIPCEntry (keccak : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨hashAUIPCPC keccak, hashAUIPCBits keccak,
    .UTYPE (hashAUIPCImmediate keccak, .Regidx (register (hashAUIPCMode keccak)), .AUIPC),
    ⟨.machine, 0, 0, register (hashAUIPCMode keccak), Word.ofBitVec (hashAUIPCImmediate keccak ++ (0 : BitVec 12)), 4, 0⟩⟩
private def hashAUIPCBefore (keccak : Bool) : State := wordWriteState initialState (hashAUIPCPC keccak).toNat (hashAUIPCBits keccak)
private def hashAUIPCAssignment (keccak : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then (hashAUIPCPC keccak).toNat
  else if column = 30 then (hashAUIPCPC keccak).toNat + 4
  else if column = 11 then 0
  else if column = 13 then 1
  else if column = 8 then if keccak then 61440 else 0
  else if column = 9 then if keccak then 65535 else 0
  else if column = 52 || column = 53 then if keccak then 1 else 0
  else assignment (hashAUIPCMode keccak) column
private def hashAUIPCRow (keccak : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, hashAUIPCAssignment keccak⟩
private def hashAUIPCData (keccak : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data (hashAUIPCMode keccak) with machine := { (data (hashAUIPCMode keccak)).machine with
      rows := [hashAUIPCRow keccak]
      rom := UnifiedReduced.Setup.table (hashAUIPCBefore keccak)
      initial := (hashAUIPCRow keccak).start
      terminal := (hashAUIPCRow keccak).finish } }

private theorem hashAUIPCCore (keccak : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (hashAUIPCAssignment keccak))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (hashAUIPCBefore keccak))) := by
  cases keccak <;> simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, hashAUIPCAssignment, hashAUIPCPC, hashAUIPCMode,
    assignment, register, low, high, Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem hashAUIPCClocks (keccak : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (hashAUIPCAssignment keccak)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases keccak <;> decide +kernel

private theorem hashAUIPCAccepted (keccak : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (hashAUIPCData keccak) [hashAUIPCEntry keccak] := by
  constructor
  · constructor
    · intro current member
      have same : current = hashAUIPCRow keccak := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append (hashAUIPCCore keccak) (hashAUIPCClocks keccak)
    · intro current member
      have same : current = hashAUIPCRow keccak := List.mem_singleton.mp member
      subst current
      cases keccak <;> decide +kernel
    · exact List.Perm.swap _ _ []
    · intro _ member
      have empty : (hashAUIPCData keccak).callers = [] := by cases keccak <;> decide +kernel
      rw [empty] at member
      cases member
    · intro _ member; cases member
    · intro _ member; cases member
    · have empty : (hashAUIPCData keccak).calls = [] := by cases keccak <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same : current = hashAUIPCRow keccak := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, (hashAUIPCRow keccak).decoderQuery = ([hashAUIPCEntry keccak].get i).query
    exact ⟨0, by cases keccak <;> decide +kernel⟩
  · cases keccak <;> decide +kernel

private theorem hashAUIPCProgram (keccak : Bool) :
    UnifiedReduced.Mixed.programImage (hashAUIPCBefore keccak) [hashAUIPCPC keccak] = some [hashAUIPCEntry keccak] := by
  have bytes : (Cell.ram (hashAUIPCPC keccak)).read (hashAUIPCBefore keccak) = .ok (hashAUIPCBits keccak) (hashAUIPCBefore keccak) := by
    cases keccak <;> exact written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards (hashAUIPCBits keccak)) (hashAUIPCBefore keccak) =
      .ok (hashAUIPCEntry keccak).instruction (hashAUIPCBefore keccak) := by cases keccak <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields (hashAUIPCEntry keccak).instruction = some (hashAUIPCEntry keccak).data := by
    cases keccak <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem hashAUIPCImage (keccak : Bool) : initialImage (hashAUIPCBefore keccak) (cells (hashAUIPCMode keccak)) =
    some (hashAUIPCData keccak).machine.initialMemory := by
  have control : (Cell.register (register (hashAUIPCMode keccak))).read (hashAUIPCBefore keccak) =
      .ok 65537 (hashAUIPCBefore keccak) := by
    cases keccak <;> apply read_register
    all_goals simp [hashAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read (hashAUIPCBefore keccak) = .ok 0 (hashAUIPCBefore keccak) := rfl
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, control, bind, Option.bind]
  cases keccak <;> rfl

private theorem hashAUIPCInputs (keccak : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (hashAUIPCData keccak)
    [hashAUIPCEntry keccak] (hashAUIPCBefore keccak) [] [hashAUIPCPC keccak] (cells (hashAUIPCMode keccak)) := by
  refine ⟨⟨rfl, ?_, ?_⟩, hashAUIPCProgram keccak, hashAUIPCImage keccak, ?_, ?_, rfl, rfl, ?_⟩
  · cases keccak <;> change 4 < timestampBase ∧ 0 < timestampBase <;> norm_num [timestampBase]
  · cases keccak <;> decide +kernel
  · cases keccak <;> decide +kernel
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  · intro _ member; cases member

private theorem hashAUIPCScope (keccak : Bool) : UnifiedReduced.Caller.PCRelativePreparation (hashAUIPCData keccak)
    [hashAUIPCEntry keccak] 8 (hashAUIPCSpan keccak).controlRegister (hashAUIPCImmediate keccak) := by
  refine ⟨⟨?_, ?_⟩, ?_, rfl, ?_, ?_⟩
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact .sequential (.arithmetic (.auipc _ _))
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    cases keccak <;> decide +kernel
  · intro entry member _
    have same := List.mem_singleton.mp member
    subst entry
    cases keccak <;> rfl
  · cases keccak <;> decide +kernel
  · cases keccak <;> decide +kernel

theorem auipc_hash_protocol_preparation (keccak : Bool) :
    UnifiedReduced.Caller.HashControlPreparation (hashAUIPCData keccak) [hashAUIPCEntry keccak] 8 (hashAUIPCSpan keccak) := by
  refine .pcRelative (hashAUIPCImmediate keccak) (hashAUIPCScope keccak) ?_
  intro entry member _
  have same := List.mem_singleton.mp member
  subst entry
  cases keccak <;> decide +kernel

theorem auipc_hash_protocol_actual_control (keccak : Bool) :
    UnifiedReduced.Caller.PreparedBoundaryExecution (hashAUIPCData keccak) (hashAUIPCBefore keccak)
      (cells (hashAUIPCMode keccak)) 8 (hashAUIPCSpan keccak).controlRegister
      (UnifiedReduced.Caller.hashPreparation (hashAUIPCSpan keccak)) :=
  UnifiedReduced.Caller.hash_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (hashAUIPCAccepted keccak) (hashAUIPCInputs keccak) (auipc_hash_protocol_preparation keccak) (by decide)

/-- Actual G/Keccak entry reads, canonical tokens and clock six follow from the
    public AUIPC placements, including Keccak's wrapped PC-plus-immediate reset. -/
theorem auipc_hash_protocol_actual_states (keccak : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atCut : State),
      events.Perm (((hashAUIPCData keccak).prefixSteps 8).map transferEvent) ∧
      SailHistory (cells (hashAUIPCMode keccak)) events (hashAUIPCBefore keccak) atCut ∧
      (Cell.register (hashAUIPCSpan keccak).controlRegister).read (hashAUIPCBefore keccak) = .ok 65537 (hashAUIPCBefore keccak) ∧
      (Cell.register (hashAUIPCSpan keccak).controlRegister).read atCut = .ok (hashAUIPCSpan keccak).controlStart atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register (hashAUIPCSpan keccak).controlRegister).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = Word.ofBitVec (hashAUIPCSpan keccak).controlStart := by
  have window := UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 8) (upper := 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (hashAUIPCAccepted keccak) (hashAUIPCInputs keccak) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨tokens, _, events, _, atCut, _, permutation, _, history, _, matching, _, boundary, _⟩ := window.execution
  obtain ⟨token, member, address, time, word⟩ := UnifiedReduced.Caller.Proofs.hash_control_preparation_token
    (by decide +kernel) (by decide +kernel) (hashAUIPCInputs keccak).setup (hashAUIPCAccepted keccak)
    (hashAUIPCInputs keccak).publicProgram (hashAUIPCInputs keccak).ordinaryProgram (hashAUIPCInputs keccak).initialization
    (auipc_hash_protocol_preparation keccak) (by decide) matching
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary member
  have same : cell = Cell.register (hashAUIPCSpan keccak).controlRegister := Trace.Proofs.cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = (hashAUIPCSpan keccak).controlStart := by rw [word, Word.ofBitVec_roundtrip]
  have initial : (Cell.register (hashAUIPCSpan keccak).controlRegister).read (hashAUIPCBefore keccak) = .ok 65537 (hashAUIPCBefore keccak) := by
    cases keccak <;> apply read_register
    all_goals simp [hashAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  exact ⟨tokens, events, atCut, permutation, history, initial, bits ▸ read, token, member, address, time, word⟩

theorem auipc_hash_wrong_public_placement_rejected :
    ¬ (∀ entry ∈ [hashAUIPCEntry false],
      entry.pc = UnifiedReduced.Caller.wrappedProgramAddress (hashAUIPCData false) (8 - 4) →
      entry.pc + (hashAUIPCImmediate false ++ (0 : BitVec 12)) =
        (Delegation.Caller.HashSpan.blakeG false).controlStart) := by
  intro placement
  have wrong := placement (hashAUIPCEntry false) (List.mem_singleton_self _) (by decide +kernel)
  exact (by decide : (128 : BitVec 32) ≠ 0) wrong

theorem auipc_incomplete_computed_hash_span_rejected (keccak : Bool) :
    ¬ UnifiedReduced.Caller.ComputedPreparedHashWindowInputs (hashAUIPCData keccak) (hashAUIPCBefore keccak)
      [] [hashAUIPCPC keccak] (cells (hashAUIPCMode keccak)) [hashAUIPCEntry keccak] (hashAUIPCSpan keccak) 8 8 := by
  intro inputs
  have count := inputs.calls
  cases keccak
  · change 0 = 56 at count
    contradiction
  · change 0 = 649 at count
    contradiction

end Tests.ControlPreparation
