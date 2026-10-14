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

end Tests.ControlPreparation
