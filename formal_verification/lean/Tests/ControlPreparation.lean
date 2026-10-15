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

private theorem hashAUIPCPublicContext (keccak : Bool) :
    UnifiedReduced.Caller.WrappedProgramComputedHashInputs (hashAUIPCData keccak) (hashAUIPCBefore keccak)
      [] [hashAUIPCPC keccak] (cells (hashAUIPCMode keccak)) [hashAUIPCEntry keccak] := by
  have context := hashAUIPCInputs keccak
  refine ⟨⟨context.publicProgram, context.ordinaryProgram, context.initialization, context.distinct,
    context.aligned, context.setup, context.tables⟩, (hashAUIPCScope keccak).registry, ?_⟩
  intro _ member; cases member

/-- Native preparation witnesses inhabit the new public context. Their empty
    selected region derives zero callers and workers without a count premise. -/
theorem auipc_public_preparation_empty_window (keccak : Bool) :
    UnifiedReduced.Caller.ProgramCallerWindow (hashAUIPCData keccak) (hashAUIPCSpan keccak).family 8 8 ∧
      ((hashAUIPCData keccak).windowMachineRows 8 8).length = 0 ∧
      ((hashAUIPCData keccak).workers.windowRows 8 8).length = 0 := by
  have context := hashAUIPCPublicContext keccak
  have region : UnifiedReduced.Caller.WrappedProgramCallerRegion (hashAUIPCData keccak)
      [hashAUIPCEntry keccak] (hashAUIPCSpan keccak).family 8 8 := by
    constructor
    · intro _ _ _ lower upper; omega
    · intro _ _ _ lower upper; omega
  have schedule := UnifiedReduced.Caller.hash_prepared_public_window_schedule_soundness
    (by decide +kernel) (by decide +kernel) context.setup (hashAUIPCAccepted keccak)
    context.publicProgram context.ordinaryProgram context.registry (auipc_hash_protocol_preparation keccak)
    region (by decide) (by decide) (by decide) (by cases keccak <;> decide +kernel)
  refine ⟨schedule, ?_, ?_⟩
  · simpa using schedule.machineCount
  · rw [← schedule.workerCount]
    simpa using schedule.machineCount

theorem auipc_public_region_including_preparation_rejected (keccak : Bool) :
    ¬ UnifiedReduced.Caller.WrappedProgramCallerRegion (hashAUIPCData keccak)
      [hashAUIPCEntry keccak] (hashAUIPCSpan keccak).family 4 8 := by
  intro region
  exact region.ordinary (hashAUIPCEntry keccak) (List.mem_singleton_self _) 4
    (by decide) (by decide) (by cases keccak <;> decide +kernel)

/-- Correct preparation and a valid empty region cannot replace the complete
    reference duration, now that worker counts are derived from public code. -/
theorem auipc_public_incomplete_hash_span_rejected (keccak : Bool) :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedHashWindowInputs (hashAUIPCData keccak)
      [hashAUIPCEntry keccak] ⟨hashAUIPCSpan keccak, 8, 8⟩ := by
  intro scope
  have duration := scope.duration
  cases keccak
  · change 8 = 8 + 4 * 56 at duration
    omega
  · change 8 = 8 + 4 * 649 at duration
    omega

/-- Supplying the full public duration cannot extend these preparation-only
    witnesses beyond their native terminal clock. -/
theorem auipc_public_hash_span_past_terminal_rejected (keccak : Bool) :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedHashWindowInputs (hashAUIPCData keccak)
      [hashAUIPCEntry keccak] ⟨hashAUIPCSpan keccak, 8, 8 + 4 * (hashAUIPCSpan keccak).callCount⟩ := by
  intro scope
  have bound := scope.beforeTerminal
  cases keccak
  · change 232 ≤ 8 at bound
    omega
  · change 2604 ≤ 8 at bound
    omega

private def roundAUIPCEntry : UnifiedReduced.ProgramEntry :=
  ⟨524288, 0x00000617, .UTYPE (0, .Regidx 12, .AUIPC), ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 4, 0⟩⟩
private def roundAUIPCBefore : State := wordWriteState initialState 524288 0x00000617
private def roundAUIPCAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 || column = 31 then 8
  else if column = 8 || column = 9 || column = 11 then 0
  else if column = 13 then 1
  else assignment 1 column
private def roundAUIPCRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, roundAUIPCAssignment⟩
private def roundAUIPCData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 1 with machine := { (data 1).machine with
      rows := [roundAUIPCRow]
      rom := UnifiedReduced.Setup.table roundAUIPCBefore
      initial := roundAUIPCRow.start
      terminal := roundAUIPCRow.finish } }

private theorem roundAUIPCCore : FlatOperation.ConstraintsHoldFlat
    (Verification.environment roundAUIPCAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table roundAUIPCBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, roundAUIPCAssignment, assignment,
    register, low, high, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem roundAUIPCClocks : FlatOperation.ConstraintsHoldFlat
    (Verification.environment roundAUIPCAssignment) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel

private theorem roundAUIPCAccepted : UnifiedReduced.Caller.MixedMemoryAccepted roundAUIPCData [roundAUIPCEntry] := by
  constructor
  · constructor
    · intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append roundAUIPCCore roundAUIPCClocks
    · intro current member
      have same := List.mem_singleton.mp member
      subst current
      decide +kernel
    · exact List.Perm.swap _ _ []
    · intro _ member
      have empty : roundAUIPCData.callers = [] := by decide +kernel
      rw [empty] at member
      cases member
    · intro _ member; cases member
    · intro _ member; cases member
    · have empty : roundAUIPCData.calls = [] := by decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, roundAUIPCRow.decoderQuery = ([roundAUIPCEntry].get i).query
    exact ⟨0, by decide +kernel⟩
  · decide +kernel

private theorem roundAUIPCProgram : UnifiedReduced.Mixed.programImage roundAUIPCBefore [524288] = some [roundAUIPCEntry] := by
  have bytes : (Cell.ram 524288).read roundAUIPCBefore = .ok 0x00000617 roundAUIPCBefore := written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00000617) roundAUIPCBefore =
      .ok roundAUIPCEntry.instruction roundAUIPCBefore := by with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields roundAUIPCEntry.instruction = some roundAUIPCEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem roundAUIPCImage : initialImage roundAUIPCBefore (cells 1) = some roundAUIPCData.machine.initialMemory := by
  have control : (Cell.register 12).read roundAUIPCBefore = .ok 65537 roundAUIPCBefore := by
    apply read_register
    simp [roundAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read roundAUIPCBefore = .ok 0 roundAUIPCBefore := rfl
  simp only [initialImage, cells, register, show (1 : Fin 3).val = 1 from rfl, show ¬(1 : Nat) = 2 by decide,
    if_false, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  rfl

private theorem roundAUIPCInputs : UnifiedReduced.Caller.MixedMemoryInputs roundAUIPCData [roundAUIPCEntry]
    roundAUIPCBefore [] [524288] (cells 1) := by
  refine ⟨⟨rfl, ?_, by decide +kernel⟩, roundAUIPCProgram, roundAUIPCImage,
    (inputs 1).distinct, (inputs 1).aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro _ member; cases member

private theorem roundAUIPCScope : UnifiedReduced.Caller.PCRelativePreparation roundAUIPCData [roundAUIPCEntry] 8 12 0 := by
  refine ⟨⟨?_, ?_⟩, ?_, rfl, by decide +kernel, by decide +kernel⟩
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact .sequential (.arithmetic (.auipc _ _))
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    decide +kernel
  · intro entry member _
    have same := List.mem_singleton.mp member
    subst entry
    rfl

theorem auipc_round_protocol_preparation :
    UnifiedReduced.Caller.HashControlPreparation roundAUIPCData [roundAUIPCEntry] 8 (.blakeRound 0) := by
  refine .pcRelative 0 roundAUIPCScope ?_
  intro entry member _
  have same := List.mem_singleton.mp member
  subst entry
  decide +kernel

theorem auipc_round_actual_control :
    (Cell.register 12).read roundAUIPCBefore = .ok 65537 roundAUIPCBefore ∧
      UnifiedReduced.Caller.PreparedBoundaryExecution roundAUIPCData roundAUIPCBefore (cells 1) 8 12
        (UnifiedReduced.Caller.hashPreparation (.blakeRound 0)) := by
  refine ⟨?_, ?_⟩
  · apply read_register
    simp [roundAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  · exact UnifiedReduced.Caller.hash_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) roundAUIPCAccepted roundAUIPCInputs auipc_round_protocol_preparation (by decide)

private theorem roundAUIPCContext : UnifiedReduced.Caller.ProtocolContextInputs roundAUIPCData
    roundAUIPCBefore [] [524288] (cells 1) [roundAUIPCEntry] :=
  ⟨roundAUIPCInputs.publicProgram, roundAUIPCInputs.ordinaryProgram, roundAUIPCInputs.initialization,
    roundAUIPCInputs.distinct, roundAUIPCInputs.aligned, roundAUIPCInputs.setup, roundAUIPCInputs.tables⟩

private theorem roundAUIPCRegion : UnifiedReduced.Caller.WrappedProgramComputedRoundRegionInputs
    roundAUIPCData [roundAUIPCEntry] ⟨0, 8, 8⟩ := by
  refine ⟨⟨?_, ?_⟩, auipc_round_protocol_preparation, by decide, by decide, by decide +kernel⟩
  · intro _ _ _ lower upper
    dsimp only at lower upper
    omega
  · intro _ _ _ lower upper
    dsimp only at lower upper
    omega

theorem auipc_round_public_empty_region :
    UnifiedReduced.Caller.ComputedRoundRegionInputs roundAUIPCData [roundAUIPCEntry] ⟨0, 8, 8⟩ ∧
      ∀ row ∈ roundAUIPCData.workers.windowRows 8 8,
        ∃ round, Blake2Round.Memory.RoundMask row.assignment round :=
  UnifiedReduced.Caller.wrapped_program_computed_round_region_soundness (by decide +kernel) (by decide +kernel)
    roundAUIPCAccepted roundAUIPCContext roundAUIPCScope.registry roundAUIPCRegion

theorem auipc_round_public_wrong_flags_rejected :
    ¬ (∀ entry ∈ [roundAUIPCEntry],
      entry.pc = UnifiedReduced.Caller.wrappedProgramAddress roundAUIPCData (8 - 4) →
      entry.pc + ((0 : BitVec 20) ++ (0 : BitVec 12)) = (Delegation.Caller.HashSpan.blakeRound 1).controlStart) := by
  intro placement
  have wrong := placement roundAUIPCEntry (List.mem_singleton_self _) (by decide +kernel)
  exact (by decide : (524288 : BitVec 32) ≠ 589824) wrong

theorem auipc_round_public_bad_cuts_rejected :
    (¬ UnifiedReduced.Caller.WrappedProgramComputedRoundRegionInputs roundAUIPCData [roundAUIPCEntry] ⟨0, 8, 52⟩) ∧
    (¬ UnifiedReduced.Caller.WrappedProgramComputedRoundRegionInputs roundAUIPCData [roundAUIPCEntry] ⟨0, 12, 8⟩) ∧
    (¬ UnifiedReduced.Caller.WrappedProgramComputedRoundRegionInputs roundAUIPCData [roundAUIPCEntry] ⟨0, 8, 10⟩) := by
  refine ⟨fun scope => ?_, fun scope => ?_, fun scope => ?_⟩
  · have extent := scope.extent.2
    norm_num at extent
  · have extent := scope.extent.1
    norm_num at extent
  · have aligned := scope.aligned.2
    norm_num at aligned

theorem auipc_round_global_memory :
    UnifiedReduced.Caller.MixedMemoryInputs roundAUIPCData [roundAUIPCEntry] roundAUIPCBefore [] [524288] (cells 1) := by
  have context : UnifiedReduced.Caller.ComputedPreparedProtocolInputs roundAUIPCData roundAUIPCBefore
      [] [524288] (cells 1) [roundAUIPCEntry] [⟨0, 8, 8⟩] := by
    refine ⟨roundAUIPCContext, ?_, ?_⟩
    · intro region member
      have same := List.mem_singleton.mp member
      subst region
      exact auipc_round_public_empty_region.1
    · intro _ member; cases member
  exact UnifiedReduced.Caller.computed_protocol_memory_soundness (by decide +kernel) (by decide +kernel)
    roundAUIPCAccepted context

theorem computed_round_region_two_bits_rejected [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedReduced.Caller.RequestTrace p} {initial : State} {ca oa : List (BitVec 32)} {domain : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    {region : UnifiedReduced.Caller.RoundRegion}
    (accepted : UnifiedReduced.Caller.MixedMemoryAccepted trace program)
    (context : UnifiedReduced.Caller.ProtocolContextInputs trace initial ca oa domain program)
    (scope : UnifiedReduced.Caller.ComputedRoundRegionInputs trace program region)
    {worker : Delegation.Row p} (member : worker ∈ trace.workers.windowRows region.lower region.upper)
    {first last : Fin 10} (different : first ≠ last)
    (firstBit : worker.assignment Blake2Round.Variables.roundBits[first] = 1)
    (lastBit : worker.assignment Blake2Round.Variables.roundBits[last] = 1) : False := by
  obtain ⟨round, mask⟩ := UnifiedReduced.Caller.computed_round_region_masks_soundness hp clockInverse accepted context scope worker member
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  by_cases same : first = round
  · have other : last ≠ round := by omega
    have zero := mask last
    rw [if_neg other, lastBit] at zero
    exact one_ne_zero zero
  · have zero := mask first
    rw [if_neg same, firstBit] at zero
    exact one_ne_zero zero

theorem auipc_round_public_protocol_context :
    UnifiedReduced.Caller.WrappedProgramComputedPreparedProtocolInputs roundAUIPCData roundAUIPCBefore
      [] [524288] (cells 1) [roundAUIPCEntry] [⟨0, 8, 8⟩] := by
  refine ⟨roundAUIPCContext, roundAUIPCScope.registry, ?_, ?_⟩
  · intro region member
    have same := List.mem_singleton.mp member
    subst region
    exact roundAUIPCRegion
  · intro _ member; cases member

theorem auipc_round_public_occurrence_coverage :
    UnifiedReduced.Caller.RoundWorkerCoverage roundAUIPCData [⟨0, 8, 8⟩] := by
  have code : UnifiedReduced.Caller.WrappedProgramRoundCallerCoverage roundAUIPCData [⟨0, 8, 8⟩] := by
    intro _ member; cases member
  exact (UnifiedReduced.Caller.wrapped_program_computed_round_coverage_soundness
    (by decide +kernel) (by decide +kernel) roundAUIPCAccepted roundAUIPCContext roundAUIPCScope.registry
    auipc_round_public_protocol_context.scopes code).1

theorem auipc_round_incomplete_protocol_reference_rejected :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs roundAUIPCData [roundAUIPCEntry] ⟨.blakeRound 0, 8, 8⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 10 at count
  contradiction

theorem auipc_round_public_incomplete_protocol_reference_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedProtocolWindowInputs roundAUIPCData [roundAUIPCEntry]
      ⟨.blakeRound 0, 8, 8⟩ := by
  intro scope
  have duration := scope.duration
  change 8 = 8 + 4 * 10 at duration
  omega

theorem auipc_round_public_protocol_reference_past_terminal_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedProtocolWindowInputs roundAUIPCData [roundAUIPCEntry]
      ⟨.blakeRound 0, 8, 48⟩ := by
  intro scope
  have bound := scope.beforeTerminal
  change 48 ≤ 8 at bound
  omega

private def registerImmediate (negative : Bool) : BitVec 12 := if negative then 0xfff else 128
private def registerBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x08060613
private def registerValue (negative : Bool) : BitVec 32 := if negative then 65536 else 65665
private def registerEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, registerBits negative, .ITYPE (registerImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (registerImmediate negative)), 1, 0⟩⟩
private def registerBefore (negative : Bool) : State := wordWriteState initialState 0 (registerBits negative)
private def registerAssignment (negative : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 5 then 12
  else if column = 36 || column = 37 || column = 51 then 1
  else if column = 46 then 4
  else if column = 40 then 0
  else if column = 8 then if negative then 65535 else 128
  else if column = 9 then if negative then 65535 else 0
  else if column = 50 then if negative then 0 else 129
  else if column = 52 || column = 53 then if negative then 1 else 0
  else assignment 0 column
private def registerRow (negative : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, registerAssignment negative⟩
private def registerData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [registerRow negative]
      rom := UnifiedReduced.Setup.table (registerBefore negative)
      initial := (registerRow negative).start
      terminal := (registerRow negative).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
        ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (if negative then 0 else 129) 1⟩] } }

private theorem registerCore (negative : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (registerAssignment negative))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (registerBefore negative))) := by
  cases negative <;> simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, registerAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem registerClocks (negative : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (registerAssignment negative)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> decide +kernel

private theorem registerAccepted (negative : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (registerData negative) [registerEntry negative] := by
  constructor
  · constructor
    · intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact Verification.holds_append (registerCore negative) (registerClocks negative)
    · intro current member
      have same := List.mem_singleton.mp member
      subst current
      cases negative <;> decide +kernel
    · exact List.Perm.swap _ _ []
    · intro _ member
      have empty : (registerData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro _ member; cases member
    · intro _ member; cases member
    · have empty : (registerData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have same := List.mem_singleton.mp member
    subst current
    change ∃ i : Fin 1, (registerRow negative).decoderQuery = ([registerEntry negative].get i).query
    exact ⟨0, by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem registerProgram (negative : Bool) : UnifiedReduced.Mixed.programImage (registerBefore negative) [0] = some [registerEntry negative] := by
  have bytes : (Cell.ram 0).read (registerBefore negative) = .ok (registerBits negative) (registerBefore negative) := written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards (registerBits negative)) (registerBefore negative) =
      .ok (registerEntry negative).instruction (registerBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields (registerEntry negative).instruction = some (registerEntry negative).data := by
    cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem registerImage (negative : Bool) : initialImage (registerBefore negative) (cells 0) = some (registerData negative).machine.initialMemory := by
  have control : (Cell.register 12).read (registerBefore negative) = .ok 65537 (registerBefore negative) := by
    apply read_register
    simp [registerBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read (registerBefore negative) = .ok 0 (registerBefore negative) := rfl
  change initialImage (registerBefore negative) [.register 0, .register 12] = _
  simp only [initialImage, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  rfl

private theorem registerInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (registerData negative)
    [registerEntry negative] (registerBefore negative) [] [0] (cells 0) := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, registerProgram negative, registerImage negative,
    (inputs 0).distinct, (inputs 0).aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro _ member; cases member

private theorem registerScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation (registerData negative)
    [registerEntry negative] 8 12 12 (registerImmediate negative) := by
  refine ⟨⟨?_, ?_⟩, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    exact .sequential (.arithmetic (.addi _ _ _))
  · intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    change (0 : Nat) % 4 = 0
    decide
  · intro entry member _
    have same := List.mem_singleton.mp member
    subst entry
    rfl

theorem register_addi_preparation (negative : Bool) :
    UnifiedReduced.Caller.RegisterImmediatePreparedBoundaryExecution (registerData negative) (registerBefore negative)
      (cells 0) 8 12 12 (registerImmediate negative) :=
  UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (registerAccepted negative) (registerInputs negative) (registerScope negative) (by decide) (by decide)

theorem register_addi_actual_states (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((registerData negative).prefixSteps 4).map transferEvent) ∧
      SailHistory (cells 0) events (registerBefore negative) atSource ∧
      SailHistory (cells 0) (rowEvents 1 (registerRow negative)).reverse atSource atCut ∧
      ((registerData negative).machine.initialMemory ++ ((registerData negative).prefixSteps 8).map Prod.snd).Perm
        (tokens ++ ((registerData negative).prefixSteps 8).map Prod.fst) ∧
      (Cell.register 12).read atSource = .ok 65537 atSource ∧
      (Cell.register 12).read atCut = .ok (registerValue negative) atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 6 ∧ token.word = Word.ofBitVec (registerValue negative) := by
  obtain ⟨row, member, _, tokens, events, atSource, atCut, permutation, past, native, matching, value, read, written, token, present, address, time, word⟩ :=
    register_addi_preparation negative
  have same := List.mem_singleton.mp member
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := registerAssignment negative)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (registerAssignment negative)) = 65537 := by
    cases negative <;> decide +kernel
  rw [operand] at actual
  have equal : value = 65537 := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue 65537 (registerImmediate negative) = registerValue negative := by
    cases negative <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, matching, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem register_addi_wrong_immediate_rejected :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (registerData false) [registerEntry false] 8 12 12 129 := by
  intro scope
  have instruction := scope.atCut (registerEntry false) (List.mem_singleton_self _) (by decide +kernel)
  have immediate := congrArg Prod.fst (SailRV32.instruction.ITYPE.inj instruction)
  exact (by decide : (128 : BitVec 12) ≠ 129) immediate

private def forgedRegisterData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { registerData false with machine := { (registerData false).machine with
      rows := [⟨.machine, fun column => if column = 36 then 2 else registerAssignment false column⟩] } }

theorem register_addi_fabricated_source_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedRegisterData [registerEntry false] := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 2 1⟩
  have member : token ∈ forgedRegisterData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedRegisterData.machine.initialMemory ++ forgedRegisterData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

private def dataflowSeed (negative : Bool) : BitVec 12 := if negative then 129 else 127
private def dataflowImmediate (negative : Bool) : BitVec 12 := if negative then 0xfff else 1
private def dataflowSeedBits (negative : Bool) : BitVec 32 := if negative then 0x08100613 else 0x07f00613
private def dataflowBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
private def dataflowBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (dataflowBits negative)
private def dataflowSeedEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, dataflowSeedBits negative, (.addi (dataflowSeed negative) : UnifiedReduced.Caller.ControlLiteral).instruction 12,
    ⟨.machine, 0, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowSeed negative)), 1, 0⟩⟩
private def dataflowEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, dataflowBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def dataflowProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, dataflowEntry negative]
private def dataflowAssignment (negative second : Bool) (column : Nat) : ZMod babyBearModulus :=
  if second then
    if column = 0 then 4
    else if column = 2 || column = 30 || column = 46 then 8
    else if column = 32 then 12
    else if column = 5 then 12
    else if column = 34 then 6
    else if column = 40 then 5
    else if column = 36 || column = 48 then if negative then 129 else 127
    else if column = 49 then 0
    else if column = 8 then if negative then 65535 else 1
    else if column = 9 then if negative then 65535 else 0
    else if column = 52 || column = 53 then if negative then 1 else 0
    else assignment 0 column
  else if column = 8 || column = 50 then if negative then 129 else 127
    else assignment 0 column
private def dataflowRow (negative second : Bool) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, dataflowAssignment negative second⟩
private def dataflowData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [dataflowRow negative true, dataflowRow negative false]
      rom := UnifiedReduced.Setup.table (dataflowBefore negative)
      terminal := (dataflowRow negative true).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (9, 0), 0⟩,
        ⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 128 0⟩] } }

private theorem dataflowCore (negative second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (dataflowAssignment negative second))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (dataflowBefore negative))) := by
  cases negative <;> cases second
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem dataflowClocks (negative second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (dataflowAssignment negative second)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> cases second <;> decide +kernel

private theorem dataflowAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (dataflowData negative) (dataflowProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = dataflowRow negative true ∨ current = dataflowRow negative false := by
        simpa [dataflowData] using member
      rcases rows with rfl | rfl
      · exact Verification.holds_append (dataflowCore negative true) (dataflowClocks negative true)
      · exact Verification.holds_append (dataflowCore negative false) (dataflowClocks negative false)
    · intro current member
      have rows : current = dataflowRow negative true ∨ current = dataflowRow negative false := by
        simpa [dataflowData] using member
      rcases rows with rfl | rfl <;> cases negative <;> decide +kernel
    · change [(dataflowRow negative false).start, (dataflowRow negative true).finish, (dataflowRow negative false).finish].Perm
        [(dataflowRow negative true).finish, (dataflowRow negative true).start, (dataflowRow negative false).start]
      have same : (dataflowRow negative false).finish = (dataflowRow negative true).start := by cases negative <;> rfl
      rw [same]
      exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
    · intro current member
      have empty : (dataflowData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (dataflowData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = dataflowRow negative true ∨ current = dataflowRow negative false := by
      simpa [dataflowData] using member
    rcases rows with rfl | rfl
    · change ∃ i : Fin 2, (dataflowRow negative true).decoderQuery = ((dataflowProgram negative).get i).query
      exact ⟨1, by cases negative <;> decide +kernel⟩
    · change ∃ i : Fin 2, (dataflowRow negative false).decoderQuery = ((dataflowProgram negative).get i).query
      exact ⟨0, by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem dataflowImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (dataflowBefore negative) [0, 4] = some (dataflowProgram negative) := by
  have first : (Cell.ram 0).read (dataflowBefore negative) = .ok (dataflowSeedBits negative) (dataflowBefore negative) :=
    written_word_disjoint 4 (dataflowBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative))
  have second : (Cell.ram 4).read (dataflowBefore negative) = .ok (dataflowBits negative) (dataflowBefore negative) :=
    written_word_read _ 4 (dataflowBits negative)
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (dataflowBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (dataflowBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (dataflowBits negative)) (dataflowBefore negative) =
      .ok (dataflowEntry negative).instruction (dataflowBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (dataflowEntry negative).instruction =
      some (dataflowEntry negative).data := by cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, decodeFirst, decodeSecond, fieldsFirst, fieldsSecond, bind, Option.bind, pure]
  rfl

private theorem dataflowInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (dataflowData negative) (dataflowProgram negative) (dataflowBefore negative) [] [0, 4] (cells 0) := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, dataflowImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (dataflowBefore negative) = .ok 0 (dataflowBefore negative) := by with_unfolding_all rfl
    have control : (Cell.register 12).read (dataflowBefore negative) = .ok 65537 (dataflowBefore negative) := by
      apply rX_register_frame (before := initialState) (after := dataflowBefore negative) rfl 12
      apply read_register
      simp [initialState, Std.ExtDHashMap.get?_insert]
    change initialImage (dataflowBefore negative) [.register 0, .register 12] = some (dataflowData negative).machine.initialMemory
    simp only [initialImage, zero, control, List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 12 := by simpa [cells, register] using member
    rcases choices with rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem dataflowRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (dataflowProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = dataflowEntry negative := by
      simpa [dataflowProgram] using member
    rcases entries with rfl | rfl
    all_goals exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = dataflowEntry negative := by
      simpa [dataflowProgram] using member
    rcases entries with rfl | rfl <;> cases negative <;> decide

private theorem dataflowScope (negative : Bool) : UnifiedReduced.Caller.LiteralAddiPreparation
    (dataflowData negative) (dataflowProgram negative) 12 12 12 (.addi (dataflowSeed negative)) (dataflowImmediate negative) := by
  refine ⟨⟨.wrappedSequential (by decide) (dataflowBefore negative) rfl (dataflowRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩,
    ⟨dataflowRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩,
    by decide, ?_⟩
  · intro current member address
    have entries : current = dataflowSeedEntry negative ∨ current = dataflowEntry negative := by
      simpa [dataflowProgram] using member
    rcases entries with rfl | rfl
    · rfl
    · have impossible : (4 : BitVec 32) = 0 := by
        cases negative <;> change (4 : BitVec 32) = 0 at address <;> exact address
      exact False.elim (by contradiction)
  · intro current member address
    have entries : current = dataflowSeedEntry negative ∨ current = dataflowEntry negative := by
      simpa [dataflowProgram] using member
    rcases entries with rfl | rfl
    · have impossible : (0 : BitVec 32) = 4 := by cases negative <;> change (0 : BitVec 32) = 4 at address <;> exact address
      exact False.elim (by contradiction)
    · rfl
  · rw [Trace.Proofs.image_addresses (dataflowInputs negative).initialization]
    exact (dataflowInputs negative).distinct

theorem literal_addi_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (dataflowData negative) (dataflowProgram negative) 12 (.blakeG true) :=
  .literalAddi 12 (.addi (dataflowSeed negative)) (dataflowImmediate negative) (dataflowScope negative)
    (by cases negative <;> decide +kernel)

theorem literal_addi_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (dataflowData negative) (dataflowBefore negative) (cells 0) 12 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.hash_control_preparation_soundness (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (dataflowAccepted negative) (dataflowInputs negative) (literal_addi_protocol_source negative) (by decide)

theorem literal_addi_operand_comes_from_seed (negative : Bool) :
    (readToken (dataflowAssignment negative true) UnifiedReduced.importedConstraintsMemoryPorts[0]).word =
      Word.ofBitVec (if negative then 129 else 127) := by
  have word := UnifiedReduced.Caller.Proofs.literal_addi_source_word (by decide +kernel) (by decide +kernel) rfl
    (dataflowAccepted negative) (dataflowInputs negative).publicProgram (dataflowInputs negative).ordinaryProgram
    (dataflowInputs negative).initialization (dataflowScope negative) (by decide) (by decide)
    (w := dataflowAssignment negative true) (by simp [dataflowData, dataflowRow])
    (by
      have empty : (dataflowData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty]
      simp)
    (by cases negative <;> decide +kernel)
  have seed : (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value =
      (if negative then 129 else 127) := by cases negative <;> decide +kernel
  exact seed ▸ word

theorem literal_addi_wrong_protocol_value_rejected (negative : Bool) :
    UnifiedReduced.Caller.registerImmediateValue
      (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value (dataflowImmediate negative) ≠
      Delegation.Caller.HashSpan.controlStart (.blakeG false) := by
  cases negative <;> decide +kernel

theorem literal_addi_actual_states (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((dataflowData negative).prefixSteps 8).map transferEvent) ∧
      SailHistory (cells 0) events (dataflowBefore negative) atSource ∧
      SailHistory (cells 0) (rowEvents 1 (dataflowRow negative true)).reverse atSource atCut ∧
      ((dataflowData negative).machine.initialMemory ++ ((dataflowData negative).prefixSteps 12).map Prod.snd).Perm
        (tokens ++ ((dataflowData negative).prefixSteps 12).map Prod.fst) ∧
      (Cell.register 12).read (dataflowBefore negative) = .ok 65537 (dataflowBefore negative) ∧
      (Cell.register 12).read atSource = .ok (if negative then 129 else 127) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 10 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, matching,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (dataflowAccepted negative) (dataflowInputs negative) (dataflowScope negative).step (by decide) (by decide)
  have same : row = dataflowRow negative true := by
    have choices : row = dataflowRow negative true ∨ row = dataflowRow negative false := by
      simpa [dataflowData] using member
    rcases choices with same | rfl
    · exact same
    · have impossible : 8 = 12 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := dataflowAssignment negative true)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  change (Cell.register 12).read atSource =
    .ok (readToken (dataflowAssignment negative true) UnifiedReduced.importedConstraintsMemoryPorts[0]).word.toBitVec atSource at actual
  rw [literal_addi_operand_comes_from_seed, Word.ofBitVec_roundtrip] at actual
  have equal : value = (if negative then 129 else 127) := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (if negative then 129 else 127) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  have initial : (Cell.register 12).read (dataflowBefore negative) = .ok 65537 (dataflowBefore negative) := by
    apply read_register
    simp [dataflowBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, matching, initial, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem literal_addi_public_empty_region (negative : Bool) :
    UnifiedReduced.Caller.ProgramCallerWindow (dataflowData negative) (Delegation.Caller.HashSpan.blakeG true).family 12 12 := by
  apply UnifiedReduced.Caller.Proofs.wrapped_program_hash_preparation_schedule (by decide +kernel) (by decide +kernel)
    (dataflowInputs negative).setup (dataflowAccepted negative) (dataflowInputs negative).publicProgram
    (dataflowInputs negative).ordinaryProgram (dataflowRegistry negative) (literal_addi_protocol_source negative)
  · constructor
    all_goals intro entry member clock lower upper
    all_goals omega
  · decide
  · decide
  · decide
  · cases negative <;> decide +kernel

theorem literal_addi_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (dataflowData negative) (dataflowProgram negative)
      ⟨.blakeG true, 12, 12⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

theorem literal_addi_wrong_immediate_rejected :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (dataflowData false) (dataflowProgram false) 12 12 12 2 := by
  intro scope
  have instruction := scope.atCut (dataflowEntry false) (by simp [dataflowProgram]) (by decide +kernel)
  have immediate := congrArg Prod.fst (SailRV32.instruction.ITYPE.inj instruction)
  exact (by decide : (1 : BitVec 12) ≠ 2) immediate

private def forgedDataflowData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { dataflowData false with machine := { (dataflowData false).machine with
      rows := [⟨.machine, fun column => if column = 36 then 128 else dataflowAssignment false true column⟩,
        dataflowRow false false] } }

theorem literal_addi_fabricated_source_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedDataflowData (dataflowProgram false) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair 128 0⟩
  have member : token ∈ forgedDataflowData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedDataflowData.machine.initialMemory ++ forgedDataflowData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

private def chainBits (negative : Bool) : BitVec 32 := if negative then 0xfff60513 else 0x00160513
private def chainBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (chainBits negative)) 8 0x00050613
private def chainMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, chainBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 10, .ADDI),
    ⟨.machine, 12, 0, 10, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def chainLastEntry : UnifiedReduced.ProgramEntry :=
  ⟨8, 0x00050613, .ITYPE (0, .Regidx 10, .Regidx 12, .ADDI), ⟨.machine, 10, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
private def chainProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, chainMiddleEntry negative, chainLastEntry]
private def chainCells : List Cell := [.register 0, .register 10, .register 12]
private def chainAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 0 then dataflowAssignment negative false column
  else if stage = 1 then
    if column = 7 || column = 44 then 10
    else if column = 46 then 0
    else if column = 48 || column = 49 then 1
    else dataflowAssignment negative true column
  else
    if column = 0 then 8
    else if column = 2 || column = 30 then 12
    else if column = 32 then 16
    else if column = 5 then 10
    else if column = 34 then 10
    else if column = 40 then 9
    else if column = 46 then 8
    else if column = 36 || column = 50 then 128
    else if column = 48 then if negative then 129 else 127
    else if column = 49 then 0
    else if column = 8 || column = 9 || column = 50 then 0
    else assignment 0 column
private def chainRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, chainAssignment negative stage⟩
private def chainData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [chainRow negative 2, chainRow negative 1, chainRow negative 0]
      rom := UnifiedReduced.Setup.table (chainBefore negative)
      terminal := (chainRow negative 2).finish
      initialMemory := [(Cell.register 0).initialToken 0, (Cell.register 10).initialToken 65537, (Cell.register 12).initialToken 65537]
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (12, 0), Nat.pair 128 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem chainCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (chainAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (chainBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem chainClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (chainAssignment negative stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> fin_cases stage <;> decide +kernel

private theorem chainAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (chainData negative) (chainProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = chainRow negative 2 ∨ current = chainRow negative 1 ∨ current = chainRow negative 0 := by
        simpa [chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (chainCore negative 2) (chainClocks negative 2)
      · exact Verification.holds_append (chainCore negative 1) (chainClocks negative 1)
      · exact Verification.holds_append (chainCore negative 0) (chainClocks negative 0)
    · intro current member
      have rows : current = chainRow negative 2 ∨ current = chainRow negative 1 ∨ current = chainRow negative 0 := by
        simpa [chainData] using member
      rcases rows with rfl | rfl | rfl <;> cases negative <;> decide +kernel
    · change [(chainRow negative 0).start, (chainRow negative 2).finish,
          (chainRow negative 1).finish, (chainRow negative 0).finish].Perm
        [(chainRow negative 2).finish, (chainRow negative 2).start,
          (chainRow negative 1).start, (chainRow negative 0).start]
      have first : (chainRow negative 0).finish = (chainRow negative 1).start := by cases negative <;> rfl
      have second : (chainRow negative 1).finish = (chainRow negative 2).start := by cases negative <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (chainData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (chainData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = chainRow negative 2 ∨ current = chainRow negative 1 ∨ current = chainRow negative 0 := by
      simpa [chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem chainImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (chainBefore negative) [0, 4, 8] = some (chainProgram negative) := by
  have first : (Cell.ram 0).read (chainBefore negative) = .ok (dataflowSeedBits negative) (chainBefore negative) :=
    written_word_disjoint 8 0x00050613 (by decide)
      (written_word_disjoint 4 (chainBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative)))
  have second : (Cell.ram 4).read (chainBefore negative) = .ok (chainBits negative) (chainBefore negative) :=
    written_word_disjoint 8 0x00050613 (by decide) (written_word_read _ 4 (chainBits negative))
  have third : (Cell.ram 8).read (chainBefore negative) = .ok 0x00050613 (chainBefore negative) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (chainBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (chainBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (chainBits negative)) (chainBefore negative) =
      .ok (chainMiddleEntry negative).instruction (chainBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards 0x00050613) (chainBefore negative) =
      .ok chainLastEntry.instruction (chainBefore negative) := by with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (chainMiddleEntry negative).instruction =
      some (chainMiddleEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields chainLastEntry.instruction = some chainLastEntry.data := by with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  rfl

private theorem chainInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (chainData negative) (chainProgram negative) (chainBefore negative) [] [0, 4, 8] chainCells := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, chainImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (chainBefore negative) = .ok 0 (chainBefore negative) := by with_unfolding_all rfl
    have regs (reg : BitVec 5) (same : reg = 10 ∨ reg = 12) :
        (Cell.register reg).read (chainBefore negative) = .ok 65537 (chainBefore negative) := by
      apply rX_register_frame (before := initialState) (after := chainBefore negative) rfl reg
      rcases same with rfl | rfl
      all_goals apply read_register
      all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, chainCells, zero, regs 10 (Or.inl rfl), regs 12 (Or.inr rfl),
      List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 := by simpa [chainCells] using member
    rcases choices with rfl | rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem chainRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (chainProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = chainMiddleEntry negative ∨ current = chainLastEntry := by
      simpa [chainProgram] using member
    rcases entries with rfl | rfl | rfl
    all_goals exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = chainMiddleEntry negative ∨ current = chainLastEntry := by
      simpa [chainProgram] using member
    rcases entries with rfl | rfl | rfl <;> cases negative <;> decide

private theorem chainSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
    (chainData negative) (chainProgram negative) 8 12 (.addi (dataflowSeed negative)) := by
  refine ⟨.wrappedSequential (by decide) (chainBefore negative) rfl (chainRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = chainMiddleEntry negative ∨ current = chainLastEntry := by
    simpa [chainProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem chainMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (chainData negative) (chainProgram negative) 12 12 10 (dataflowImmediate negative) := by
  refine ⟨chainRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = chainMiddleEntry negative ∨ current = chainLastEntry := by
    simpa [chainProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · rfl
  · change (8 : BitVec 32) = 4 at address
    contradiction

private theorem chainLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (chainData negative) (chainProgram negative) 16 10 12 0 := by
  refine ⟨chainRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = chainMiddleEntry negative ∨ current = chainLastEntry := by
    simpa [chainProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl

private def chainValue (negative : Bool) : BitVec 32 := UnifiedReduced.Caller.registerImmediateValue
  (UnifiedReduced.Caller.registerImmediateValue (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
    (dataflowImmediate negative)) 0
private theorem chainPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterPreparation
    (chainData negative) (chainProgram negative) 16 12 (chainValue negative) :=
  .addi (.addi (.literal (chainSeedScope negative)) (chainMiddleScope negative) (by decide)) (chainLastScope negative) (by decide)

theorem public_register_chain_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterChainPreparedBoundaryExecution
    (chainData negative) (chainBefore negative) chainCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_chain_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (chainAccepted negative) (chainInputs negative) (chainPreparation negative) (by decide) (by decide)
  have value : chainValue negative = 128 := by cases negative <;> decide +kernel
  exact value ▸ result

theorem public_register_chain_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (chainData negative) (chainProgram negative) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_chain_hash_preparation_source (chainInputs negative).initialization
    (chainInputs negative).distinct (chainPreparation negative) (by cases negative <;> decide +kernel)

theorem public_register_chain_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (chainData negative) (chainBefore negative) chainCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_chain_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (chainAccepted negative) (chainInputs negative) (chainPreparation negative)
    (by cases negative <;> decide +kernel) (by decide)

theorem public_register_chain_wrong_value_rejected (negative : Bool) : chainValue negative ≠
    (Delegation.Caller.HashSpan.blakeG false).controlStart := by cases negative <;> decide +kernel

theorem public_register_chain_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (chainData negative) (chainProgram negative) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

theorem public_register_chain_actual_states (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((chainData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (chainBefore negative) atSource ∧
      SailHistory chainCells (rowEvents 1 (chainRow negative 2)).reverse atSource atCut ∧
      ((chainData negative).machine.initialMemory ++ ((chainData negative).prefixSteps 16).map Prod.snd).Perm
        (tokens ++ ((chainData negative).prefixSteps 16).map Prod.fst) ∧
      (Cell.register 10).read atSource = .ok 128 atSource ∧
      (Cell.register 12).read atSource = .ok (if negative then 129 else 127) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, matching,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (chainAccepted negative) (chainInputs negative) (chainLastScope negative) (by decide) (by decide)
  have same : row = chainRow negative 2 := by
    have choices : row = chainRow negative 2 ∨ row = chainRow negative 1 ∨ row = chainRow negative 0 := by
      simpa [chainData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by cases negative <;> exact last
      omega
    · have impossible : 8 = 16 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := chainAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 10) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have old := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := chainAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[2]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (chainAssignment negative 2)) = 128 := by
    cases negative <;> decide +kernel
  have oldValue : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[2].readCode (chainAssignment negative 2)) =
      (if negative then 129 else 127) := by cases negative <;> decide +kernel
  rw [operand] at actual
  rw [oldValue] at old
  have equal : value = 128 := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue 128 0 = 128 := by decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, matching, actual, old, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_register_chain_wrong_immediate_rejected :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (chainData false) (chainProgram false) 16 10 12 1 := by
  intro scope
  have instruction := scope.atCut chainLastEntry (by simp [chainProgram]) (by decide +kernel)
  have immediate := congrArg Prod.fst (SailRV32.instruction.ITYPE.inj instruction)
  exact (by decide : (0 : BitVec 12) ≠ 1) immediate

private def forgedChainData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [chainRow negative 2,
        ⟨.machine, fun column => if column = 36 then (if negative then 130 else 128) else chainAssignment negative 1 column⟩,
        chainRow negative 0] } }

theorem public_register_chain_fabricated_middle_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (forgedChainData negative) (chainProgram negative) := by
  intro accepted
  let token : MemoryToken babyBearModulus :=
    ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (if negative then 130 else 128) 0⟩
  have member : token ∈ (forgedChainData negative).mixedSteps.map Prod.fst := by cases negative <;> decide +kernel
  have absent : token ∉ (forgedChainData negative).machine.initialMemory ++ (forgedChainData negative).mixedSteps.map Prod.snd := by
    cases negative <;> decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

theorem auipc_public_register_chain_preparation (keccak : Bool) :
    UnifiedReduced.Caller.RegisterChainPreparedBoundaryExecution (hashAUIPCData keccak) (hashAUIPCBefore keccak)
      (cells (hashAUIPCMode keccak)) 8 (hashAUIPCSpan keccak).controlRegister (hashAUIPCSpan keccak).controlStart := by
  have preparation := UnifiedReduced.Caller.PublicRegisterPreparation.pcRelative (hashAUIPCScope keccak)
  have result := UnifiedReduced.Caller.register_chain_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (hashAUIPCAccepted keccak) (hashAUIPCInputs keccak) preparation
    (by cases keccak <;> decide) (by decide)
  have value : UnifiedReduced.Caller.pcRelativeControl (hashAUIPCData keccak) 8 (hashAUIPCImmediate keccak) =
      (hashAUIPCSpan keccak).controlStart := by cases keccak <;> decide +kernel
  exact value ▸ result

private def gapBits (_negative : Bool) : BitVec 32 := 0x00060513
private def gapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
private def gapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (gapBits negative)) 8 (gapLastBits negative)
private def gapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, gapBits negative, .ITYPE (0, .Regidx 12, .Regidx 10, .ADDI), ⟨.machine, 12, 0, 10, ⟨0, 0⟩, 1, 0⟩⟩
private def gapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, gapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def gapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, gapMiddleEntry negative, gapLastEntry negative]
private def gapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 8 || column = 9 || column = 52 || column = 53 then 0
    else if column = 50 then if negative then 129 else 127
    else chainAssignment negative stage column
  else if stage = 2 then
    if column = 5 then 12
    else if column = 34 then 8
    else if column = 46 then 12
    else if column = 36 then if negative then 129 else 127
    else if column = 8 then if negative then 65535 else 1
    else if column = 9 then if negative then 65535 else 0
    else if column = 52 || column = 53 then if negative then 1 else 0
    else chainAssignment negative stage column
  else chainAssignment negative stage column
private def gapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, gapAssignment negative stage⟩
private def gapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [gapRow negative 2, gapRow negative 1, gapRow negative 0]
      rom := UnifiedReduced.Setup.table (gapBefore negative)
      terminal := (gapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 127) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem gapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (gapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (gapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem gapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (gapAssignment negative stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> fin_cases stage <;> decide +kernel

private theorem gapAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (gapData negative) (gapProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = gapRow negative 2 ∨ current = gapRow negative 1 ∨ current = gapRow negative 0 := by
        simpa [gapData, chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (gapCore negative 2) (gapClocks negative 2)
      · exact Verification.holds_append (gapCore negative 1) (gapClocks negative 1)
      · exact Verification.holds_append (gapCore negative 0) (gapClocks negative 0)
    · intro current member
      have rows : current = gapRow negative 2 ∨ current = gapRow negative 1 ∨ current = gapRow negative 0 := by
        simpa [gapData, chainData] using member
      rcases rows with rfl | rfl | rfl <;> cases negative <;> decide +kernel
    · change [(gapRow negative 0).start, (gapRow negative 2).finish,
          (gapRow negative 1).finish, (gapRow negative 0).finish].Perm
        [(gapRow negative 2).finish, (gapRow negative 2).start,
          (gapRow negative 1).start, (gapRow negative 0).start]
      have first : (gapRow negative 0).finish = (gapRow negative 1).start := by cases negative <;> rfl
      have second : (gapRow negative 1).finish = (gapRow negative 2).start := by cases negative <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (gapData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (gapData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = gapRow negative 2 ∨ current = gapRow negative 1 ∨ current = gapRow negative 0 := by
      simpa [gapData, chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem gapImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (gapBefore negative) [0, 4, 8] = some (gapProgram negative) := by
  have first : (Cell.ram 0).read (gapBefore negative) = .ok (dataflowSeedBits negative) (gapBefore negative) :=
    written_word_disjoint 8 (gapLastBits negative) (by decide)
      (written_word_disjoint 4 (gapBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative)))
  have second : (Cell.ram 4).read (gapBefore negative) = .ok (gapBits negative) (gapBefore negative) :=
    written_word_disjoint 8 (gapLastBits negative) (by decide) (written_word_read _ 4 (gapBits negative))
  have third : (Cell.ram 8).read (gapBefore negative) = .ok (gapLastBits negative) (gapBefore negative) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (gapBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (gapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (gapBits negative)) (gapBefore negative) =
      .ok (gapMiddleEntry negative).instruction (gapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards (gapLastBits negative)) (gapBefore negative) =
      .ok (gapLastEntry negative).instruction (gapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (gapMiddleEntry negative).instruction =
      some (gapMiddleEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields (gapLastEntry negative).instruction = some (gapLastEntry negative).data := by cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  rfl

private theorem gapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (gapData negative) (gapProgram negative) (gapBefore negative) [] [0, 4, 8] chainCells := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, gapImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (gapBefore negative) = .ok 0 (gapBefore negative) := by with_unfolding_all rfl
    have regs (reg : BitVec 5) (same : reg = 10 ∨ reg = 12) :
        (Cell.register reg).read (gapBefore negative) = .ok 65537 (gapBefore negative) := by
      apply rX_register_frame (before := initialState) (after := gapBefore negative) rfl reg
      rcases same with rfl | rfl
      all_goals apply read_register
      all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, chainCells, zero, regs 10 (Or.inl rfl), regs 12 (Or.inr rfl),
      List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 := by simpa [chainCells] using member
    rcases choices with rfl | rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem gapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (gapProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = gapMiddleEntry negative ∨ current = gapLastEntry negative := by
      simpa [gapProgram] using member
    rcases entries with rfl | rfl | rfl
    all_goals exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = gapMiddleEntry negative ∨ current = gapLastEntry negative := by
      simpa [gapProgram] using member
    rcases entries with rfl | rfl | rfl <;> cases negative <;> decide

private theorem gapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
    (gapData negative) (gapProgram negative) 8 12 (.addi (dataflowSeed negative)) := by
  refine ⟨.wrappedSequential (by decide) (gapBefore negative) rfl (gapRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = gapMiddleEntry negative ∨ current = gapLastEntry negative := by
    simpa [gapProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem gapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (gapData negative) (gapProgram negative) 12 12 10 0 := by
  refine ⟨gapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = gapMiddleEntry negative ∨ current = gapLastEntry negative := by
    simpa [gapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · rfl
  · change (8 : BitVec 32) = 4 at address
    contradiction

private theorem gapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (gapData negative) (gapProgram negative) 16 12 12 (dataflowImmediate negative) := by
  refine ⟨gapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = gapMiddleEntry negative ∨ current = gapLastEntry negative := by
    simpa [gapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl


private def gapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
private theorem gapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (gapData negative) (gapProgram negative) 12 12 (gapValue negative) :=
  .frame (.prepared (.literal (gapSeedScope negative))) (gapMiddleScope negative) (by decide) (by decide)
private theorem gapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (gapData negative) (gapProgram negative) 16 12
      (UnifiedReduced.Caller.registerImmediateValue (gapValue negative) (dataflowImmediate negative)) :=
  .addi (gapFramed negative) (gapLastScope negative) (by decide)

theorem public_dataflow_gap_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (gapData negative) (gapBefore negative) chainCells 12 12 (gapValue negative) :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapAccepted negative) (gapInputs negative) (gapFramed negative) (by decide) (by decide)

theorem public_dataflow_final_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (gapData negative) (gapBefore negative) chainCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapAccepted negative) (gapInputs negative) (gapPreparation negative) (by decide) (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (gapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact value ▸ result

theorem public_dataflow_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (gapData negative) (gapProgram negative) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (gapInputs negative).initialization
    (gapInputs negative).distinct (gapFramed negative) (gapLastScope negative) (by decide)
    (by cases negative <;> decide +kernel)

theorem public_dataflow_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (gapData negative) (gapBefore negative) chainCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapAccepted negative) (gapInputs negative) (gapFramed negative) (gapLastScope negative)
    (by decide) (by cases negative <;> decide +kernel) (by decide)

theorem public_dataflow_gap_retains_refresh_and_write (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm (((gapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (gapBefore negative) atGap ∧
      (Cell.register 10).read (gapBefore negative) = .ok 65537 (gapBefore negative) ∧
      (Cell.register 12).read atGap = .ok (gapValue negative) atGap ∧
      (Cell.register 10).read atGap = .ok (gapValue negative) atGap ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 8 ∧ token.word = Word.ofBitVec (gapValue negative) := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (gapAccepted negative) (gapInputs negative)
      (by decide) (by decide) (by decide) (by decide)).execution
  let refresh : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (8, 0), Nat.pair (if negative then 129 else 127) 0⟩
  let copied : MemoryToken babyBearModulus := ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 127) 0⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ (gapData negative).machine.initialMemory ++ ((gapData negative).prefixSteps 12).map Prod.snd)
      (notRead : token ∉ ((gapData negative).prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have refreshPresent : refresh ∈ tokens := actual refresh (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  have copyPresent : copied ∈ tokens := actual copied (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary refreshPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, copyRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary copyPresent
  have same : cell = Cell.register 10 := Trace.Proofs.cell_address_injective code
  subst cell
  have refreshWord : refresh.word = Word.ofBitVec (gapValue negative) := by cases negative <;> decide +kernel
  have copyWord : copied.word = Word.ofBitVec (gapValue negative) := by cases negative <;> decide +kernel
  rw [refreshWord, Word.ofBitVec_roundtrip] at read
  rw [copyWord, Word.ofBitVec_roundtrip] at copyRead
  have initial : (Cell.register 10).read (gapBefore negative) = .ok 65537 (gapBefore negative) := by
    apply read_register
    simp [gapBefore, wordWriteState, initialState]
  exact ⟨tokens, events, atGap, permutation, history, initial, read, copyRead,
    refresh, refreshPresent, rfl, by cases negative <;> decide, refreshWord⟩

theorem public_dataflow_actual_final_cycle (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((gapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (gapBefore negative) atSource ∧
      SailHistory chainCells (rowEvents 1 (gapRow negative 2)).reverse atSource atCut ∧
      (Cell.register 12).read atSource = .ok (gapValue negative) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, _,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (gapAccepted negative) (gapInputs negative) (gapLastScope negative) (by decide) (by decide)
  have same : row = gapRow negative 2 := by
    have choices : row = gapRow negative 2 ∨ row = gapRow negative 1 ∨ row = gapRow negative 0 := by
      simpa [gapData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by cases negative <;> exact last
      omega
    · have impossible : 8 = 16 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := gapAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (gapAssignment negative 2)) = gapValue negative := by
    cases negative <;> decide +kernel
  rw [operand] at actual
  have equal : value = gapValue negative := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (gapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_dataflow_wrong_value_rejected (negative : Bool) :
    UnifiedReduced.Caller.registerImmediateValue (gapValue negative) (dataflowImmediate negative) ≠
      (Delegation.Caller.HashSpan.blakeG false).controlStart := by cases negative <;> decide +kernel

theorem public_dataflow_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (gapData negative) (gapProgram negative) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

private def forgedGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { gapData negative with machine := { (gapData negative).machine with
      rows := [⟨.machine, fun column => if column = 34 then 10 else gapAssignment negative 2 column⟩,
        gapRow negative 1, gapRow negative 0] } }

theorem public_dataflow_fabricated_fresh_source_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (forgedGapData negative) (gapProgram negative) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (10, 0), Nat.pair (if negative then 129 else 127) 0⟩
  have member : token ∈ (forgedGapData negative).mixedSteps.map Prod.fst := by cases negative <;> decide +kernel
  have absent : token ∉ (forgedGapData negative).machine.initialMemory ++ (forgedGapData negative).mixedSteps.map Prod.snd := by
    cases negative <;> decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

theorem public_dataflow_fabricated_fresh_source_native (negative : Bool) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 34 then 10 else gapAssignment negative 2 column))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (gapBefore negative)) ++
        UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · cases negative
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, gapAssignment, chainAssignment, assignment, register,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | (refine ⟨(0 : Fin 2097537), ?_⟩
         change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
           (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases negative <;> decide +kernel

private def arithmeticGapBits (negative : Bool) : BitVec 32 := if negative then 0x40c60533 else 0x00c60533
private def arithmeticGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
private def arithmeticGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (arithmeticGapBits negative)) 8 (arithmeticGapLastBits negative)
private def arithmeticGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, arithmeticGapBits negative, .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, if negative then .SUB else .ADD),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, if negative then 2 else 1, 0⟩⟩
private def arithmeticGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, arithmeticGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def arithmeticGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, arithmeticGapMiddleEntry negative, arithmeticGapLastEntry negative]
private def arithmeticGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 6 || column = 38 then 12
    else if column = 40 then 8
    else if column = 42 then if negative then 129 else 127
    else if column = 11 then if negative then 0 else 1
    else if column = 12 then if negative then 1 else 0
    else if column = 50 then if negative then 0 else 254
    else if column = 80 then if negative then 943710600 else 943710840
    else gapAssignment negative stage column
  else if stage = 2 then
    if column = 34 then 9
    else if column = 40 then 5
    else gapAssignment negative stage column
  else gapAssignment negative stage column
private def arithmeticGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, arithmeticGapAssignment negative stage⟩
private def arithmeticGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [arithmeticGapRow negative 2, arithmeticGapRow negative 1, arithmeticGapRow negative 0]
      rom := UnifiedReduced.Setup.table (arithmeticGapBefore negative)
      terminal := (arithmeticGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 0 else 254) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem arithmeticGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmeticGapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (arithmeticGapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, arithmeticGapAssignment, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem arithmeticGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (arithmeticGapAssignment negative stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> fin_cases stage <;> decide +kernel

private theorem arithmeticGapAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (arithmeticGapData negative) (arithmeticGapProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = arithmeticGapRow negative 2 ∨ current = arithmeticGapRow negative 1 ∨ current = arithmeticGapRow negative 0 := by
        simpa [arithmeticGapData, chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (arithmeticGapCore negative 2) (arithmeticGapClocks negative 2)
      · exact Verification.holds_append (arithmeticGapCore negative 1) (arithmeticGapClocks negative 1)
      · exact Verification.holds_append (arithmeticGapCore negative 0) (arithmeticGapClocks negative 0)
    · intro current member
      have rows : current = arithmeticGapRow negative 2 ∨ current = arithmeticGapRow negative 1 ∨ current = arithmeticGapRow negative 0 := by
        simpa [arithmeticGapData, chainData] using member
      rcases rows with rfl | rfl | rfl <;> cases negative <;> decide +kernel
    · change [(arithmeticGapRow negative 0).start, (arithmeticGapRow negative 2).finish,
          (arithmeticGapRow negative 1).finish, (arithmeticGapRow negative 0).finish].Perm
        [(arithmeticGapRow negative 2).finish, (arithmeticGapRow negative 2).start,
          (arithmeticGapRow negative 1).start, (arithmeticGapRow negative 0).start]
      have first : (arithmeticGapRow negative 0).finish = (arithmeticGapRow negative 1).start := by cases negative <;> rfl
      have second : (arithmeticGapRow negative 1).finish = (arithmeticGapRow negative 2).start := by cases negative <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (arithmeticGapData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (arithmeticGapData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = arithmeticGapRow negative 2 ∨ current = arithmeticGapRow negative 1 ∨ current = arithmeticGapRow negative 0 := by
      simpa [arithmeticGapData, chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem arithmeticGapImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (arithmeticGapBefore negative) [0, 4, 8] = some (arithmeticGapProgram negative) := by
  have first : (Cell.ram 0).read (arithmeticGapBefore negative) = .ok (dataflowSeedBits negative) (arithmeticGapBefore negative) :=
    written_word_disjoint 8 (arithmeticGapLastBits negative) (by decide)
      (written_word_disjoint 4 (arithmeticGapBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative)))
  have second : (Cell.ram 4).read (arithmeticGapBefore negative) = .ok (arithmeticGapBits negative) (arithmeticGapBefore negative) :=
    written_word_disjoint 8 (arithmeticGapLastBits negative) (by decide) (written_word_read _ 4 (arithmeticGapBits negative))
  have third : (Cell.ram 8).read (arithmeticGapBefore negative) = .ok (arithmeticGapLastBits negative) (arithmeticGapBefore negative) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (arithmeticGapBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (arithmeticGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (arithmeticGapBits negative)) (arithmeticGapBefore negative) =
      .ok (arithmeticGapMiddleEntry negative).instruction (arithmeticGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards (arithmeticGapLastBits negative)) (arithmeticGapBefore negative) =
      .ok (arithmeticGapLastEntry negative).instruction (arithmeticGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (arithmeticGapMiddleEntry negative).instruction =
      some (arithmeticGapMiddleEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields (arithmeticGapLastEntry negative).instruction = some (arithmeticGapLastEntry negative).data := by cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  rfl

private theorem arithmeticGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (arithmeticGapData negative) (arithmeticGapProgram negative) (arithmeticGapBefore negative) [] [0, 4, 8] chainCells := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, arithmeticGapImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (arithmeticGapBefore negative) = .ok 0 (arithmeticGapBefore negative) := by with_unfolding_all rfl
    have regs (reg : BitVec 5) (same : reg = 10 ∨ reg = 12) :
        (Cell.register reg).read (arithmeticGapBefore negative) = .ok 65537 (arithmeticGapBefore negative) := by
      apply rX_register_frame (before := initialState) (after := arithmeticGapBefore negative) rfl reg
      rcases same with rfl | rfl
      all_goals apply read_register
      all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, chainCells, zero, regs 10 (Or.inl rfl), regs 12 (Or.inr rfl),
      List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 := by simpa [chainCells] using member
    rcases choices with rfl | rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem arithmeticGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (arithmeticGapProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = arithmeticGapMiddleEntry negative ∨ current = arithmeticGapLastEntry negative := by
      simpa [arithmeticGapProgram] using member
    rcases entries with rfl | rfl | rfl
    · exact .sequential (.arithmetic (.addi _ _ _))
    · cases negative
      · exact .sequential (.arithmetic (.add _ _ _))
      · exact .sequential (.arithmetic (.sub _ _ _))
    · exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = arithmeticGapMiddleEntry negative ∨ current = arithmeticGapLastEntry negative := by
      simpa [arithmeticGapProgram] using member
    rcases entries with rfl | rfl | rfl <;> cases negative <;> decide

private theorem arithmeticGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
    (arithmeticGapData negative) (arithmeticGapProgram negative) 8 12 (.addi (dataflowSeed negative)) := by
  refine ⟨.wrappedSequential (by decide) (arithmeticGapBefore negative) rfl (arithmeticGapRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = arithmeticGapMiddleEntry negative ∨ current = arithmeticGapLastEntry negative := by
    simpa [arithmeticGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem arithmeticGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.ArithmeticFramePreparation
    (arithmeticGapData negative) (arithmeticGapProgram negative) 12 10 := by
  refine ⟨arithmeticGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = arithmeticGapMiddleEntry negative ∨ current = arithmeticGapLastEntry negative := by
    simpa [arithmeticGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · cases negative
    · exact .add _ _ _
    · exact .sub _ _ _
  · change (8 : BitVec 32) = 4 at address
    contradiction

private theorem arithmeticGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (arithmeticGapData negative) (arithmeticGapProgram negative) 16 12 12 (dataflowImmediate negative) := by
  refine ⟨arithmeticGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = arithmeticGapMiddleEntry negative ∨ current = arithmeticGapLastEntry negative := by
    simpa [arithmeticGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl


private def arithmeticGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
private theorem arithmeticGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (arithmeticGapData negative) (arithmeticGapProgram negative) 12 12 (arithmeticGapValue negative) :=
  .arithmeticFrame (.prepared (.literal (arithmeticGapSeedScope negative))) (arithmeticGapMiddleScope negative) (by decide) (by decide)
private theorem arithmeticGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (arithmeticGapData negative) (arithmeticGapProgram negative) 16 12
      (UnifiedReduced.Caller.registerImmediateValue (arithmeticGapValue negative) (dataflowImmediate negative)) :=
  .addi (arithmeticGapFramed negative) (arithmeticGapLastScope negative) (by decide)

theorem public_arithmetic_gap_gap_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (arithmeticGapData negative) (arithmeticGapBefore negative) chainCells 12 12 (arithmeticGapValue negative) :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (arithmeticGapAccepted negative) (arithmeticGapInputs negative) (arithmeticGapFramed negative) (by decide) (by decide)

theorem public_arithmetic_gap_final_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (arithmeticGapData negative) (arithmeticGapBefore negative) chainCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (arithmeticGapAccepted negative) (arithmeticGapInputs negative) (arithmeticGapPreparation negative) (by decide) (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (arithmeticGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact value ▸ result

theorem public_arithmetic_gap_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (arithmeticGapData negative) (arithmeticGapProgram negative) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (arithmeticGapInputs negative).initialization
    (arithmeticGapInputs negative).distinct (arithmeticGapFramed negative) (arithmeticGapLastScope negative) (by decide)
    (by cases negative <;> decide +kernel)

theorem public_arithmetic_gap_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (arithmeticGapData negative) (arithmeticGapBefore negative) chainCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (arithmeticGapAccepted negative) (arithmeticGapInputs negative) (arithmeticGapFramed negative) (arithmeticGapLastScope negative)
    (by decide) (by cases negative <;> decide +kernel) (by decide)

theorem public_arithmetic_gap_gap_retains_refresh_and_write (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm (((arithmeticGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (arithmeticGapBefore negative) atGap ∧
      (Cell.register 10).read (arithmeticGapBefore negative) = .ok 65537 (arithmeticGapBefore negative) ∧
      (Cell.register 12).read atGap = .ok (arithmeticGapValue negative) atGap ∧
      (Cell.register 10).read atGap = .ok (if negative then 0 else 254) atGap ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 9 ∧ token.word = Word.ofBitVec (arithmeticGapValue negative) := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (arithmeticGapAccepted negative) (arithmeticGapInputs negative)
      (by decide) (by decide) (by decide) (by decide)).execution
  let refresh : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (9, 0), Nat.pair (if negative then 129 else 127) 0⟩
  let copied : MemoryToken babyBearModulus := ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 0 else 254) 0⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ (arithmeticGapData negative).machine.initialMemory ++ ((arithmeticGapData negative).prefixSteps 12).map Prod.snd)
      (notRead : token ∉ ((arithmeticGapData negative).prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have refreshPresent : refresh ∈ tokens := actual refresh (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  have copyPresent : copied ∈ tokens := actual copied (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary refreshPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, copyRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary copyPresent
  have same : cell = Cell.register 10 := Trace.Proofs.cell_address_injective code
  subst cell
  have refreshWord : refresh.word = Word.ofBitVec (arithmeticGapValue negative) := by cases negative <;> decide +kernel
  have copyWord : copied.word = Word.ofBitVec (if negative then 0 else 254) := by cases negative <;> decide +kernel
  rw [refreshWord, Word.ofBitVec_roundtrip] at read
  rw [copyWord, Word.ofBitVec_roundtrip] at copyRead
  have initial : (Cell.register 10).read (arithmeticGapBefore negative) = .ok 65537 (arithmeticGapBefore negative) := by
    apply read_register
    simp [arithmeticGapBefore, wordWriteState, initialState]
  exact ⟨tokens, events, atGap, permutation, history, initial, read, copyRead,
    refresh, refreshPresent, rfl, by cases negative <;> decide, refreshWord⟩

theorem public_arithmetic_gap_actual_final_cycle (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((arithmeticGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (arithmeticGapBefore negative) atSource ∧
      SailHistory chainCells (rowEvents 1 (arithmeticGapRow negative 2)).reverse atSource atCut ∧
      (Cell.register 12).read atSource = .ok (arithmeticGapValue negative) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, _,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (arithmeticGapAccepted negative) (arithmeticGapInputs negative) (arithmeticGapLastScope negative) (by decide) (by decide)
  have same : row = arithmeticGapRow negative 2 := by
    have choices : row = arithmeticGapRow negative 2 ∨ row = arithmeticGapRow negative 1 ∨ row = arithmeticGapRow negative 0 := by
      simpa [arithmeticGapData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by cases negative <;> exact last
      omega
    · have impossible : 8 = 16 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := arithmeticGapAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (arithmeticGapAssignment negative 2)) = arithmeticGapValue negative := by
    cases negative <;> decide +kernel
  rw [operand] at actual
  have equal : value = arithmeticGapValue negative := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (arithmeticGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_arithmetic_gap_wrong_value_rejected (negative : Bool) :
    UnifiedReduced.Caller.registerImmediateValue (arithmeticGapValue negative) (dataflowImmediate negative) ≠
      (Delegation.Caller.HashSpan.blakeG false).controlStart := by cases negative <;> decide +kernel

theorem public_arithmetic_gap_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (arithmeticGapData negative) (arithmeticGapProgram negative) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

theorem public_arithmetic_gap_wrong_destination_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ArithmeticFramePreparation (arithmeticGapData negative) (arithmeticGapProgram negative) 12 12 := by
  intro scope
  have form := scope.atCut (arithmeticGapMiddleEntry negative) (by simp [arithmeticGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases form

theorem public_arithmetic_gap_wrong_instruction_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (arithmeticGapData negative) (arithmeticGapProgram negative) 12 12 10 0 := by
  intro scope
  have instruction := scope.atCut (arithmeticGapMiddleEntry negative) (by simp [arithmeticGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases instruction


private def staleArithmeticGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { arithmeticGapData negative with machine := { (arithmeticGapData negative).machine with
      rows := [⟨.machine, fun column => if column = 34 then 8 else arithmeticGapAssignment negative 2 column⟩,
        arithmeticGapRow negative 1, arithmeticGapRow negative 0] } }

/-- Clock eight really was produced, but the second aliased read already consumed
    it. Local constraints accept this stale source; global matching rejects its
    second consumption rather than inventing a fresh token. -/
theorem public_arithmetic_gap_stale_source_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (staleArithmeticGapData negative) (arithmeticGapProgram negative) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (8, 0), Nat.pair (if negative then 129 else 127) 0⟩
  have produced : ((staleArithmeticGapData negative).machine.initialMemory ++
      (staleArithmeticGapData negative).mixedSteps.map Prod.snd).count token = 1 := by cases negative <;> decide +kernel
  have consumed : ((staleArithmeticGapData negative).machine.terminalMemory ++
      (staleArithmeticGapData negative).mixedSteps.map Prod.fst).count token = 2 := by cases negative <;> decide +kernel
  have impossible : (1 : Nat) = 2 := produced.symm.trans ((accepted.memory.count_eq token).trans consumed)
  omega

theorem public_arithmetic_gap_stale_source_native (negative : Bool) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 34 then 8 else arithmeticGapAssignment negative 2 column))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (arithmeticGapBefore negative)) ++
        UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · cases negative
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, arithmeticGapAssignment, gapAssignment, chainAssignment, assignment, register,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | (refine ⟨(0 : Fin 2097537), ?_⟩
         change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
           (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases negative <;> decide +kernel

private def binaryGapBits (negative : Bool) : BitVec 32 := if negative then 0x00c67533 else 0x00c64533
private def binaryGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
private def binaryGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (binaryGapBits negative)) 8 (binaryGapLastBits negative)
private def binaryGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, binaryGapBits negative, .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, if negative then .AND else .XOR),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, 65536, if negative then 54 else 52⟩⟩
private def binaryGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, binaryGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def binaryGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, binaryGapMiddleEntry negative, binaryGapLastEntry negative]
private def binaryGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 11 || column = 12 then 0
    else if column = 27 then 1
    else if column = 10 || column = 92 || column = 101 || column = 110 || column = 119 then
      if negative then 54 else 52
    else if column = 50 || column = 58 || column = 95 then if negative then 129 else 0
    else if column = 74 || column = 76 || column = 93 || column = 94 then if negative then 129 else 127
    else if column = 88 then 3
    else arithmeticGapAssignment negative stage column
  else arithmeticGapAssignment negative stage column
private def binaryGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, binaryGapAssignment negative stage⟩
private def binaryGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [binaryGapRow negative 2, binaryGapRow negative 1, binaryGapRow negative 0]
      rom := UnifiedReduced.Setup.table (binaryGapBefore negative)
      terminal := (binaryGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 0) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem binaryGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (binaryGapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (binaryGapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, binaryGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | exact ⟨⟨1, by decide⟩, by with_unfolding_all decide +kernel⟩
    | exact ⟨⟨257, by decide⟩, by with_unfolding_all decide +kernel⟩
    | exact ⟨⟨257 + 127 * 256 + 127, by decide⟩, by with_unfolding_all decide +kernel⟩
    | exact ⟨⟨131329, by decide⟩, by with_unfolding_all decide +kernel⟩
    | exact ⟨⟨131329 + 129 * 256 + 129, by decide⟩, by with_unfolding_all decide +kernel⟩


private theorem binaryGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (binaryGapAssignment negative stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> fin_cases stage <;> decide +kernel

private theorem binaryGapAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (binaryGapData negative) (binaryGapProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = binaryGapRow negative 2 ∨ current = binaryGapRow negative 1 ∨ current = binaryGapRow negative 0 := by
        simpa [binaryGapData, chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (binaryGapCore negative 2) (binaryGapClocks negative 2)
      · exact Verification.holds_append (binaryGapCore negative 1) (binaryGapClocks negative 1)
      · exact Verification.holds_append (binaryGapCore negative 0) (binaryGapClocks negative 0)
    · intro current member
      have rows : current = binaryGapRow negative 2 ∨ current = binaryGapRow negative 1 ∨ current = binaryGapRow negative 0 := by
        simpa [binaryGapData, chainData] using member
      rcases rows with rfl | rfl | rfl <;> cases negative <;> decide +kernel
    · change [(binaryGapRow negative 0).start, (binaryGapRow negative 2).finish,
          (binaryGapRow negative 1).finish, (binaryGapRow negative 0).finish].Perm
        [(binaryGapRow negative 2).finish, (binaryGapRow negative 2).start,
          (binaryGapRow negative 1).start, (binaryGapRow negative 0).start]
      have first : (binaryGapRow negative 0).finish = (binaryGapRow negative 1).start := by cases negative <;> rfl
      have second : (binaryGapRow negative 1).finish = (binaryGapRow negative 2).start := by cases negative <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (binaryGapData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (binaryGapData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = binaryGapRow negative 2 ∨ current = binaryGapRow negative 1 ∨ current = binaryGapRow negative 0 := by
      simpa [binaryGapData, chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem binaryGapImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (binaryGapBefore negative) [0, 4, 8] = some (binaryGapProgram negative) := by
  have first : (Cell.ram 0).read (binaryGapBefore negative) = .ok (dataflowSeedBits negative) (binaryGapBefore negative) :=
    written_word_disjoint 8 (binaryGapLastBits negative) (by decide)
      (written_word_disjoint 4 (binaryGapBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative)))
  have second : (Cell.ram 4).read (binaryGapBefore negative) = .ok (binaryGapBits negative) (binaryGapBefore negative) :=
    written_word_disjoint 8 (binaryGapLastBits negative) (by decide) (written_word_read _ 4 (binaryGapBits negative))
  have third : (Cell.ram 8).read (binaryGapBefore negative) = .ok (binaryGapLastBits negative) (binaryGapBefore negative) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (binaryGapBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (binaryGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (binaryGapBits negative)) (binaryGapBefore negative) =
      .ok (binaryGapMiddleEntry negative).instruction (binaryGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards (binaryGapLastBits negative)) (binaryGapBefore negative) =
      .ok (binaryGapLastEntry negative).instruction (binaryGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (binaryGapMiddleEntry negative).instruction =
      some (binaryGapMiddleEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields (binaryGapLastEntry negative).instruction = some (binaryGapLastEntry negative).data := by cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  rfl

private theorem binaryGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (binaryGapData negative) (binaryGapProgram negative) (binaryGapBefore negative) [] [0, 4, 8] chainCells := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, binaryGapImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (binaryGapBefore negative) = .ok 0 (binaryGapBefore negative) := by with_unfolding_all rfl
    have regs (reg : BitVec 5) (same : reg = 10 ∨ reg = 12) :
        (Cell.register reg).read (binaryGapBefore negative) = .ok 65537 (binaryGapBefore negative) := by
      apply rX_register_frame (before := initialState) (after := binaryGapBefore negative) rfl reg
      rcases same with rfl | rfl
      all_goals apply read_register
      all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, chainCells, zero, regs 10 (Or.inl rfl), regs 12 (Or.inr rfl),
      List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 := by simpa [chainCells] using member
    rcases choices with rfl | rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem binaryGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (binaryGapProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = binaryGapMiddleEntry negative ∨ current = binaryGapLastEntry negative := by
      simpa [binaryGapProgram] using member
    rcases entries with rfl | rfl | rfl
    · exact .sequential (.arithmetic (.addi _ _ _))
    · cases negative
      · exact .sequential (.xor _ _ _)
      · exact .sequential (.and _ _ _)
    · exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = binaryGapMiddleEntry negative ∨ current = binaryGapLastEntry negative := by
      simpa [binaryGapProgram] using member
    rcases entries with rfl | rfl | rfl <;> cases negative <;> decide

private theorem binaryGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
    (binaryGapData negative) (binaryGapProgram negative) 8 12 (.addi (dataflowSeed negative)) := by
  refine ⟨.wrappedSequential (by decide) (binaryGapBefore negative) rfl (binaryGapRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = binaryGapMiddleEntry negative ∨ current = binaryGapLastEntry negative := by
    simpa [binaryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem binaryGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterFramePreparation
    (binaryGapData negative) (binaryGapProgram negative) 12 10 := by
  refine ⟨binaryGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = binaryGapMiddleEntry negative ∨ current = binaryGapLastEntry negative := by
    simpa [binaryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · cases negative
    · exact .binary (.xor _ _ _)
    · exact .binary (.and _ _ _)
  · change (8 : BitVec 32) = 4 at address
    contradiction

private theorem binaryGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (binaryGapData negative) (binaryGapProgram negative) 16 12 12 (dataflowImmediate negative) := by
  refine ⟨binaryGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = binaryGapMiddleEntry negative ∨ current = binaryGapLastEntry negative := by
    simpa [binaryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl


private def binaryGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
private theorem binaryGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (binaryGapData negative) (binaryGapProgram negative) 12 12 (binaryGapValue negative) :=
  .registerFrame (.prepared (.literal (binaryGapSeedScope negative))) (binaryGapMiddleScope negative) (by decide) (by decide)
private theorem binaryGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (binaryGapData negative) (binaryGapProgram negative) 16 12
      (UnifiedReduced.Caller.registerImmediateValue (binaryGapValue negative) (dataflowImmediate negative)) :=
  .addi (binaryGapFramed negative) (binaryGapLastScope negative) (by decide)

theorem public_binary_gap_gap_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (binaryGapData negative) (binaryGapBefore negative) chainCells 12 12 (binaryGapValue negative) :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (binaryGapAccepted negative) (binaryGapInputs negative) (binaryGapFramed negative) (by decide) (by decide)

theorem public_binary_gap_final_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (binaryGapData negative) (binaryGapBefore negative) chainCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (binaryGapAccepted negative) (binaryGapInputs negative) (binaryGapPreparation negative) (by decide) (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (binaryGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact value ▸ result

theorem public_binary_gap_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (binaryGapData negative) (binaryGapProgram negative) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (binaryGapInputs negative).initialization
    (binaryGapInputs negative).distinct (binaryGapFramed negative) (binaryGapLastScope negative) (by decide)
    (by cases negative <;> decide +kernel)

theorem public_binary_gap_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (binaryGapData negative) (binaryGapBefore negative) chainCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (binaryGapAccepted negative) (binaryGapInputs negative) (binaryGapFramed negative) (binaryGapLastScope negative)
    (by decide) (by cases negative <;> decide +kernel) (by decide)

theorem public_binary_gap_gap_retains_refresh_and_write (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm (((binaryGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (binaryGapBefore negative) atGap ∧
      (Cell.register 10).read (binaryGapBefore negative) = .ok 65537 (binaryGapBefore negative) ∧
      (Cell.register 12).read atGap = .ok (binaryGapValue negative) atGap ∧
      (Cell.register 10).read atGap = .ok (if negative then 129 else 0) atGap ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 9 ∧ token.word = Word.ofBitVec (binaryGapValue negative) := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (binaryGapAccepted negative) (binaryGapInputs negative)
      (by decide) (by decide) (by decide) (by decide)).execution
  let refresh : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (9, 0), Nat.pair (if negative then 129 else 127) 0⟩
  let copied : MemoryToken babyBearModulus := ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 0) 0⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ (binaryGapData negative).machine.initialMemory ++ ((binaryGapData negative).prefixSteps 12).map Prod.snd)
      (notRead : token ∉ ((binaryGapData negative).prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have refreshPresent : refresh ∈ tokens := actual refresh (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  have copyPresent : copied ∈ tokens := actual copied (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary refreshPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, copyRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary copyPresent
  have same : cell = Cell.register 10 := Trace.Proofs.cell_address_injective code
  subst cell
  have refreshWord : refresh.word = Word.ofBitVec (binaryGapValue negative) := by cases negative <;> decide +kernel
  have copyWord : copied.word = Word.ofBitVec (if negative then 129 else 0) := by cases negative <;> decide +kernel
  rw [refreshWord, Word.ofBitVec_roundtrip] at read
  rw [copyWord, Word.ofBitVec_roundtrip] at copyRead
  have initial : (Cell.register 10).read (binaryGapBefore negative) = .ok 65537 (binaryGapBefore negative) := by
    apply read_register
    simp [binaryGapBefore, wordWriteState, initialState]
  exact ⟨tokens, events, atGap, permutation, history, initial, read, copyRead,
    refresh, refreshPresent, rfl, by cases negative <;> decide, refreshWord⟩

theorem public_binary_gap_actual_final_cycle (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((binaryGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (binaryGapBefore negative) atSource ∧
      SailHistory chainCells (rowEvents 1 (binaryGapRow negative 2)).reverse atSource atCut ∧
      (Cell.register 12).read atSource = .ok (binaryGapValue negative) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, _,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (binaryGapAccepted negative) (binaryGapInputs negative) (binaryGapLastScope negative) (by decide) (by decide)
  have same : row = binaryGapRow negative 2 := by
    have choices : row = binaryGapRow negative 2 ∨ row = binaryGapRow negative 1 ∨ row = binaryGapRow negative 0 := by
      simpa [binaryGapData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by cases negative <;> exact last
      omega
    · have impossible : 8 = 16 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := binaryGapAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (binaryGapAssignment negative 2)) = binaryGapValue negative := by
    cases negative <;> decide +kernel
  rw [operand] at actual
  have equal : value = binaryGapValue negative := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (binaryGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_binary_gap_wrong_value_rejected (negative : Bool) :
    UnifiedReduced.Caller.registerImmediateValue (binaryGapValue negative) (dataflowImmediate negative) ≠
      (Delegation.Caller.HashSpan.blakeG false).controlStart := by cases negative <;> decide +kernel

theorem public_binary_gap_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (binaryGapData negative) (binaryGapProgram negative) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

theorem public_binary_gap_wrong_destination_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.RegisterFramePreparation (binaryGapData negative) (binaryGapProgram negative) 12 12 := by
  intro scope
  have form := scope.atCut (binaryGapMiddleEntry negative) (by simp [binaryGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases form <;> rename_i form
  all_goals cases form

theorem public_binary_gap_wrong_instruction_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (binaryGapData negative) (binaryGapProgram negative) 12 12 10 0 := by
  intro scope
  have instruction := scope.atCut (binaryGapMiddleEntry negative) (by simp [binaryGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases instruction


private def staleBinaryGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { binaryGapData negative with machine := { (binaryGapData negative).machine with
      rows := [⟨.machine, fun column => if column = 34 then 8 else binaryGapAssignment negative 2 column⟩,
        binaryGapRow negative 1, binaryGapRow negative 0] } }

/-- Clock eight really was produced, but the second aliased read already consumed
    it. Local constraints accept this stale source; global matching rejects its
    second consumption rather than inventing a fresh token. -/
theorem public_binary_gap_stale_source_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (staleBinaryGapData negative) (binaryGapProgram negative) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (8, 0), Nat.pair (if negative then 129 else 127) 0⟩
  have produced : ((staleBinaryGapData negative).machine.initialMemory ++
      (staleBinaryGapData negative).mixedSteps.map Prod.snd).count token = 1 := by cases negative <;> decide +kernel
  have consumed : ((staleBinaryGapData negative).machine.terminalMemory ++
      (staleBinaryGapData negative).mixedSteps.map Prod.fst).count token = 2 := by cases negative <;> decide +kernel
  have impossible : (1 : Nat) = 2 := produced.symm.trans ((accepted.memory.count_eq token).trans consumed)
  omega

theorem public_binary_gap_stale_source_native (negative : Bool) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 34 then 8 else binaryGapAssignment negative 2 column))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (binaryGapBefore negative)) ++
        UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · cases negative
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, binaryGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, assignment, register,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | (refine ⟨(0 : Fin 2097537), ?_⟩
         change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
           (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases negative <;> decide +kernel

theorem public_binary_gap_illegal_shift_rejected (kind : Fin 3) :
    UnifiedReduced.Mixed.decoderFields (.SHIFTIOP (32, .Regidx 12, .Regidx 10,
      if kind.val = 0 then .SLLI else if kind.val = 1 then .SRLI else .SRAI)) = none := by
  fin_cases kind <;> decide +kernel

theorem public_binary_gap_discarded_destination_rejected (negative : Bool) :
    UnifiedReduced.Mixed.decoderFields (.RTYPE (.Regidx 12, .Regidx 12, .Regidx 0,
      if negative then .AND else .XOR)) = none := by
  cases negative <;> decide +kernel


private def comparisonCustomGapBits (negative : Bool) : BitVec 32 := if negative then 0xc2c64573 else 0x00c63533
private def comparisonCustomGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
private def comparisonCustomGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (comparisonCustomGapBits negative)) 8 (comparisonCustomGapLastBits negative)
private def comparisonCustomGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, comparisonCustomGapBits negative,
    if negative then .ZIMOP_MOP_RR (4, .Regidx 12, .Regidx 12, .Regidx 10)
    else .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, .SLTU),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, if negative then 512 else 4096, if negative then 0 else 3⟩⟩
private def comparisonCustomGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, comparisonCustomGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
private def comparisonCustomGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, comparisonCustomGapMiddleEntry negative, comparisonCustomGapLastEntry negative]
private def comparisonCustomGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 11 || column = 12 then 0
    else if negative then
      if column = 20 then 1
      else if column = 50 then 259
      else if column = 51 then 1
      else arithmeticGapAssignment negative stage column
    else
      if column = 23 || column = 57 || column = 84 || column = 88 || column = 90 then 1
      else if column = 10 then 3
      else if column = 81 || column = 120 || column = 122 then 8
      else if column = 92 || column = 101 then 5
      else if column = 110 then 51
      else if column = 111 then 56
      else if column = 119 then 2
      else if column = 50 || column = 129 then 0
      else arithmeticGapAssignment negative stage column
  else arithmeticGapAssignment negative stage column
private def comparisonCustomGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, comparisonCustomGapAssignment negative stage⟩
private def comparisonCustomGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [comparisonCustomGapRow negative 2, comparisonCustomGapRow negative 1, comparisonCustomGapRow negative 0]
      rom := UnifiedReduced.Setup.table (comparisonCustomGapBefore negative)
      terminal := (comparisonCustomGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 259 else 0) (if negative then 1 else 0)⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem comparisonCustomGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (comparisonCustomGapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (comparisonCustomGapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, comparisonCustomGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)
    | (refine ⟨⟨524545, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨655617, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])
    | (refine ⟨⟨786745, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (refine ⟨⟨721161, by decide⟩, ?_⟩; norm_num [UnifiedReduced.Setup.row, UnifiedReduced.Setup.fixedRow])

private theorem comparisonCustomGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (comparisonCustomGapAssignment negative stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases negative <;> fin_cases stage <;> decide +kernel

private theorem comparisonCustomGapAccepted (negative : Bool) :
    UnifiedReduced.Caller.MixedMemoryAccepted (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) := by
  constructor
  · constructor
    · intro current member
      have rows : current = comparisonCustomGapRow negative 2 ∨ current = comparisonCustomGapRow negative 1 ∨ current = comparisonCustomGapRow negative 0 := by
        simpa [comparisonCustomGapData, chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (comparisonCustomGapCore negative 2) (comparisonCustomGapClocks negative 2)
      · exact Verification.holds_append (comparisonCustomGapCore negative 1) (comparisonCustomGapClocks negative 1)
      · exact Verification.holds_append (comparisonCustomGapCore negative 0) (comparisonCustomGapClocks negative 0)
    · intro current member
      have rows : current = comparisonCustomGapRow negative 2 ∨ current = comparisonCustomGapRow negative 1 ∨ current = comparisonCustomGapRow negative 0 := by
        simpa [comparisonCustomGapData, chainData] using member
      rcases rows with rfl | rfl | rfl <;> cases negative <;> decide +kernel
    · change [(comparisonCustomGapRow negative 0).start, (comparisonCustomGapRow negative 2).finish,
          (comparisonCustomGapRow negative 1).finish, (comparisonCustomGapRow negative 0).finish].Perm
        [(comparisonCustomGapRow negative 2).finish, (comparisonCustomGapRow negative 2).start,
          (comparisonCustomGapRow negative 1).start, (comparisonCustomGapRow negative 0).start]
      have first : (comparisonCustomGapRow negative 0).finish = (comparisonCustomGapRow negative 1).start := by cases negative <;> rfl
      have second : (comparisonCustomGapRow negative 1).finish = (comparisonCustomGapRow negative 2).start := by cases negative <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (comparisonCustomGapData negative).callers = [] := by cases negative <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (comparisonCustomGapData negative).calls = [] := by cases negative <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = comparisonCustomGapRow negative 2 ∨ current = comparisonCustomGapRow negative 1 ∨ current = comparisonCustomGapRow negative 0 := by
      simpa [comparisonCustomGapData, chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by cases negative <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by cases negative <;> decide +kernel⟩
  · cases negative <;> decide +kernel

private theorem comparisonCustomGapImage (negative : Bool) :
    UnifiedReduced.Mixed.programImage (comparisonCustomGapBefore negative) [0, 4, 8] = some (comparisonCustomGapProgram negative) := by
  have first : (Cell.ram 0).read (comparisonCustomGapBefore negative) = .ok (dataflowSeedBits negative) (comparisonCustomGapBefore negative) :=
    written_word_disjoint 8 (comparisonCustomGapLastBits negative) (by decide)
      (written_word_disjoint 4 (comparisonCustomGapBits negative) (by decide) (written_word_read initialState 0 (dataflowSeedBits negative)))
  have second : (Cell.ram 4).read (comparisonCustomGapBefore negative) = .ok (comparisonCustomGapBits negative) (comparisonCustomGapBefore negative) :=
    written_word_disjoint 8 (comparisonCustomGapLastBits negative) (by decide) (written_word_read _ 4 (comparisonCustomGapBits negative))
  have third : (Cell.ram 8).read (comparisonCustomGapBefore negative) = .ok (comparisonCustomGapLastBits negative) (comparisonCustomGapBefore negative) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits negative)) (comparisonCustomGapBefore negative) =
      .ok (dataflowSeedEntry negative).instruction (comparisonCustomGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (comparisonCustomGapBits negative)) (comparisonCustomGapBefore negative) =
      .ok (comparisonCustomGapMiddleEntry negative).instruction (comparisonCustomGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards (comparisonCustomGapLastBits negative)) (comparisonCustomGapBefore negative) =
      .ok (comparisonCustomGapLastEntry negative).instruction (comparisonCustomGapBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry negative).instruction =
      some (dataflowSeedEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (comparisonCustomGapMiddleEntry negative).instruction =
      some (comparisonCustomGapMiddleEntry negative).data := by cases negative <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields (comparisonCustomGapLastEntry negative).instruction = some (comparisonCustomGapLastEntry negative).data := by cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  rfl

private theorem comparisonCustomGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) (comparisonCustomGapBefore negative) [] [0, 4, 8] chainCells := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, comparisonCustomGapImage negative, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (comparisonCustomGapBefore negative) = .ok 0 (comparisonCustomGapBefore negative) := by with_unfolding_all rfl
    have regs (reg : BitVec 5) (same : reg = 10 ∨ reg = 12) :
        (Cell.register reg).read (comparisonCustomGapBefore negative) = .ok 65537 (comparisonCustomGapBefore negative) := by
      apply rX_register_frame (before := initialState) (after := comparisonCustomGapBefore negative) rfl reg
      rcases same with rfl | rfl
      all_goals apply read_register
      all_goals simp [initialState, Std.ExtDHashMap.get?_insert]
    simp only [initialImage, chainCells, zero, regs 10 (Or.inl rfl), regs 12 (Or.inr rfl),
      List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 := by simpa [chainCells] using member
    rcases choices with rfl | rfl | rfl <;> trivial
  · intro current member
    cases member

private theorem comparisonCustomGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (comparisonCustomGapProgram negative) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = comparisonCustomGapMiddleEntry negative ∨ current = comparisonCustomGapLastEntry negative := by
      simpa [comparisonCustomGapProgram] using member
    rcases entries with rfl | rfl | rfl
    · exact .sequential (.arithmetic (.addi _ _ _))
    · cases negative
      · exact .sltu _ _ _
      · exact .sequential (.triadd _ _ _)
    · exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry negative ∨ current = comparisonCustomGapMiddleEntry negative ∨ current = comparisonCustomGapLastEntry negative := by
      simpa [comparisonCustomGapProgram] using member
    rcases entries with rfl | rfl | rfl <;> cases negative <;> decide

private theorem comparisonCustomGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 8 12 (.addi (dataflowSeed negative)) := by
  refine ⟨.wrappedSequential (by decide) (comparisonCustomGapBefore negative) rfl (comparisonCustomGapRegistry negative) ?_, rfl,
    by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = comparisonCustomGapMiddleEntry negative ∨ current = comparisonCustomGapLastEntry negative := by
    simpa [comparisonCustomGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem comparisonCustomGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterFramePreparation
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 12 10 := by
  refine ⟨comparisonCustomGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = comparisonCustomGapMiddleEntry negative ∨ current = comparisonCustomGapLastEntry negative := by
    simpa [comparisonCustomGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · cases negative
    · exact .comparison (.sltu _ _ _)
    · exact .custom (.triadd _ _ _)
  · change (8 : BitVec 32) = 4 at address
    contradiction

private theorem comparisonCustomGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 16 12 12 (dataflowImmediate negative) := by
  refine ⟨comparisonCustomGapRegistry negative, ?_, rfl, by cases negative <;> decide +kernel, by cases negative <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry negative ∨ current = comparisonCustomGapMiddleEntry negative ∨ current = comparisonCustomGapLastEntry negative := by
    simpa [comparisonCustomGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl


private def comparisonCustomGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
private theorem comparisonCustomGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 12 12 (comparisonCustomGapValue negative) :=
  .registerFrame (.prepared (.literal (comparisonCustomGapSeedScope negative))) (comparisonCustomGapMiddleScope negative) (by decide) (by decide)
private theorem comparisonCustomGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 16 12
      (UnifiedReduced.Caller.registerImmediateValue (comparisonCustomGapValue negative) (dataflowImmediate negative)) :=
  .addi (comparisonCustomGapFramed negative) (comparisonCustomGapLastScope negative) (by decide)

theorem public_comparison_custom_gap_gap_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (comparisonCustomGapData negative) (comparisonCustomGapBefore negative) chainCells 12 12 (comparisonCustomGapValue negative) :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (comparisonCustomGapAccepted negative) (comparisonCustomGapInputs negative) (comparisonCustomGapFramed negative) (by decide) (by decide)

theorem public_comparison_custom_gap_final_preparation (negative : Bool) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (comparisonCustomGapData negative) (comparisonCustomGapBefore negative) chainCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (comparisonCustomGapAccepted negative) (comparisonCustomGapInputs negative) (comparisonCustomGapPreparation negative) (by decide) (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (comparisonCustomGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact value ▸ result

theorem public_comparison_custom_gap_protocol_source (negative : Bool) : UnifiedReduced.Caller.HashControlPreparation
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (comparisonCustomGapInputs negative).initialization
    (comparisonCustomGapInputs negative).distinct (comparisonCustomGapFramed negative) (comparisonCustomGapLastScope negative) (by decide)
    (by cases negative <;> decide +kernel)

theorem public_comparison_custom_gap_protocol_preparation (negative : Bool) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (comparisonCustomGapData negative) (comparisonCustomGapBefore negative) chainCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (comparisonCustomGapAccepted negative) (comparisonCustomGapInputs negative) (comparisonCustomGapFramed negative) (comparisonCustomGapLastScope negative)
    (by decide) (by cases negative <;> decide +kernel) (by decide)

theorem public_comparison_custom_gap_gap_retains_refresh_and_write (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm (((comparisonCustomGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (comparisonCustomGapBefore negative) atGap ∧
      (Cell.register 10).read (comparisonCustomGapBefore negative) = .ok 65537 (comparisonCustomGapBefore negative) ∧
      (Cell.register 12).read atGap = .ok (comparisonCustomGapValue negative) atGap ∧
      (Cell.register 10).read atGap = .ok (if negative then 65795 else 0) atGap ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 9 ∧ token.word = Word.ofBitVec (comparisonCustomGapValue negative) := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (comparisonCustomGapAccepted negative) (comparisonCustomGapInputs negative)
      (by decide) (by decide) (by decide) (by decide)).execution
  let refresh : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (9, 0), Nat.pair (if negative then 129 else 127) 0⟩
  let copied : MemoryToken babyBearModulus := ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 259 else 0) (if negative then 1 else 0)⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ (comparisonCustomGapData negative).machine.initialMemory ++ ((comparisonCustomGapData negative).prefixSteps 12).map Prod.snd)
      (notRead : token ∉ ((comparisonCustomGapData negative).prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have refreshPresent : refresh ∈ tokens := actual refresh (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  have copyPresent : copied ∈ tokens := actual copied (by cases negative <;> decide +kernel) (by cases negative <;> decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary refreshPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, copyRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary copyPresent
  have same : cell = Cell.register 10 := Trace.Proofs.cell_address_injective code
  subst cell
  have refreshWord : refresh.word = Word.ofBitVec (comparisonCustomGapValue negative) := by cases negative <;> decide +kernel
  have copyWord : copied.word = Word.ofBitVec (if negative then 65795 else 0) := by cases negative <;> decide +kernel
  rw [refreshWord, Word.ofBitVec_roundtrip] at read
  rw [copyWord, Word.ofBitVec_roundtrip] at copyRead
  have initial : (Cell.register 10).read (comparisonCustomGapBefore negative) = .ok 65537 (comparisonCustomGapBefore negative) := by
    apply read_register
    simp [comparisonCustomGapBefore, wordWriteState, initialState]
  exact ⟨tokens, events, atGap, permutation, history, initial, read, copyRead,
    refresh, refreshPresent, rfl, by cases negative <;> decide, refreshWord⟩

theorem public_comparison_custom_gap_actual_final_cycle (negative : Bool) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((comparisonCustomGapData negative).prefixSteps 12).map transferEvent) ∧
      SailHistory chainCells events (comparisonCustomGapBefore negative) atSource ∧
      SailHistory chainCells (rowEvents 1 (comparisonCustomGapRow negative 2)).reverse atSource atCut ∧
      (Cell.register 12).read atSource = .ok (comparisonCustomGapValue negative) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, _,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (comparisonCustomGapAccepted negative) (comparisonCustomGapInputs negative) (comparisonCustomGapLastScope negative) (by decide) (by decide)
  have same : row = comparisonCustomGapRow negative 2 := by
    have choices : row = comparisonCustomGapRow negative 2 ∨ row = comparisonCustomGapRow negative 1 ∨ row = comparisonCustomGapRow negative 0 := by
      simpa [comparisonCustomGapData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by cases negative <;> exact last
      omega
    · have impossible : 8 = 16 := by cases negative <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := comparisonCustomGapAssignment negative 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by cases negative <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (comparisonCustomGapAssignment negative 2)) = comparisonCustomGapValue negative := by
    cases negative <;> decide +kernel
  rw [operand] at actual
  have equal : value = comparisonCustomGapValue negative := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (comparisonCustomGapValue negative) (dataflowImmediate negative) = 128 := by
    cases negative <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_comparison_custom_gap_wrong_value_rejected (negative : Bool) :
    UnifiedReduced.Caller.registerImmediateValue (comparisonCustomGapValue negative) (dataflowImmediate negative) ≠
      (Delegation.Caller.HashSpan.blakeG false).controlStart := by cases negative <;> decide +kernel

theorem public_comparison_custom_gap_incomplete_reference_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction

theorem public_comparison_custom_gap_wrong_destination_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.RegisterFramePreparation (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 12 12 := by
  intro scope
  have form := scope.atCut (comparisonCustomGapMiddleEntry negative) (by simp [comparisonCustomGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases form <;> rename_i form
  all_goals cases form

theorem public_comparison_custom_gap_wrong_instruction_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.RegisterImmediatePreparation (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 12 12 10 0 := by
  intro scope
  have instruction := scope.atCut (comparisonCustomGapMiddleEntry negative) (by simp [comparisonCustomGapProgram]) (by cases negative <;> decide +kernel)
  cases negative <;> cases instruction


private def staleComparisonCustomGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { comparisonCustomGapData negative with machine := { (comparisonCustomGapData negative).machine with
      rows := [⟨.machine, fun column => if column = 34 then 8 else comparisonCustomGapAssignment negative 2 column⟩,
        comparisonCustomGapRow negative 1, comparisonCustomGapRow negative 0] } }

/-- Clock eight really was produced, but the second aliased read already consumed
    it. Local constraints accept this stale source; global matching rejects its
    second consumption rather than inventing a fresh token. -/
theorem public_comparison_custom_gap_stale_source_rejected (negative : Bool) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (staleComparisonCustomGapData negative) (comparisonCustomGapProgram negative) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (8, 0), Nat.pair (if negative then 129 else 127) 0⟩
  have produced : ((staleComparisonCustomGapData negative).machine.initialMemory ++
      (staleComparisonCustomGapData negative).mixedSteps.map Prod.snd).count token = 1 := by cases negative <;> decide +kernel
  have consumed : ((staleComparisonCustomGapData negative).machine.terminalMemory ++
      (staleComparisonCustomGapData negative).mixedSteps.map Prod.fst).count token = 2 := by cases negative <;> decide +kernel
  have impossible : (1 : Nat) = 2 := produced.symm.trans ((accepted.memory.count_eq token).trans consumed)
  omega

theorem public_comparison_custom_gap_stale_source_native (negative : Bool) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 34 then 8 else comparisonCustomGapAssignment negative 2 column))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (comparisonCustomGapBefore negative)) ++
        UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · cases negative
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, comparisonCustomGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, assignment, register,
      Lookup.Contains, Table.toRaw, fromElements]
    all_goals repeat' apply And.intro
    all_goals solve
      | decide +kernel
      | (apply Verification.range16_contains; decide +kernel)
      | (refine ⟨(0 : Fin 2097537), ?_⟩
         change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
           (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
         decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases negative <;> decide +kernel

theorem public_comparison_custom_gap_unsupported_mop_rejected :
    UnifiedReduced.Mixed.decoderFields (.ZIMOP_MOP_R (1, .Regidx 12, .Regidx 10)) = none ∧
    UnifiedReduced.Mixed.decoderFields (.ZIMOP_MOP_RR (3, .Regidx 12, .Regidx 12, .Regidx 10)) = none := by
  decide +kernel

theorem public_comparison_custom_gap_discarded_destination_rejected :
    UnifiedReduced.Mixed.decoderFields (.RTYPE (.Regidx 12, .Regidx 12, .Regidx 0, .SLTU)) = none ∧
    UnifiedReduced.Mixed.decoderFields (.ZIMOP_MOP_RR (4, .Regidx 12, .Regidx 12, .Regidx 0)) = none := by
  decide +kernel


end Tests.ControlPreparation
