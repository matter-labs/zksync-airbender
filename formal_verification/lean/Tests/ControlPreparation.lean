import Tests.ControlPreparationComparisonGap

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def memoryGapBits (kind : Fin 3) : BitVec 32 :=
  if kind.val = 0 then 0x00052503 else if kind.val = 1 then 0x00c52023 else 0x00262003
private def memoryGapLastBits (kind : Fin 3) : BitVec 32 := if kind.val = 1 then 0xfff60613 else 0x00160613
private def memoryGapBase : State :=
  { initialState with regs := initialState.regs.insert .x10 (4194304 : BitVec 32) }
private def memoryGapBefore (kind : Fin 3) : State :=
  wordWriteState (wordWriteState (wordWriteState (wordWriteState memoryGapBase 4194304 42)
    0 (dataflowSeedBits (memoryGapNegative kind))) 4 (memoryGapBits kind)) 8 (memoryGapLastBits kind)
private def memoryGapMiddleEntry (kind : Fin 3) : UnifiedReduced.ProgramEntry :=
  if kind.val = 0 then
    ⟨4, memoryGapBits kind, .LOAD (0, .Regidx 10, .Regidx 10, false, 4), ⟨.machine, 10, 0, 10, ⟨0, 0⟩, 131072, 0⟩⟩
  else if kind.val = 1 then
    ⟨4, memoryGapBits kind, .STORE (0, .Regidx 12, .Regidx 10, 4), ⟨.machine, 10, 12, 0, ⟨0, 0⟩, 262144, 0⟩⟩
  else
    ⟨4, memoryGapBits kind, .LOAD (2, .Regidx 12, .Regidx 0, false, 4), ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩
private theorem memoryGapMiddlePC (kind : Fin 3) : (memoryGapMiddleEntry kind).pc = 4 := by
  fin_cases kind <;> rfl
private def memoryGapLastEntry (kind : Fin 3) : UnifiedReduced.ProgramEntry :=
  ⟨8, memoryGapLastBits kind, .ITYPE (dataflowImmediate (memoryGapNegative kind), .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate (memoryGapNegative kind))), 1, 0⟩⟩
private def memoryGapProgram (kind : Fin 3) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry (memoryGapNegative kind), memoryGapMiddleEntry kind, memoryGapLastEntry kind]
private def memoryGapAssignment (kind : Fin 3) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
  if stage = 1 then
    if column = 0 then 4
    else if column = 2 || column = 30 then 8
    else if column = 32 then 12
    else if column = 4 || column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
    else if kind.val = 0 then
      if column = 5 || column = 7 || column = 44 then 10
      else if column = 28 then 1
      else if column = 37 || column = 39 || column = 49 || column = 58 then 64
      else if column = 46 then 8
      else if column = 42 || column = 50 then 42
      else if column = 80 then 4194304 * 42 * 943718400
      else 0
    else if kind.val = 1 then
      if column = 5 then 10
      else if column = 6 || column = 38 then 12
      else if column = 29 then 1
      else if column = 37 || column = 45 || column = 58 then 64
      else if column = 40 then 6
      else if column = 42 || column = 50 then 129
      else if column = 48 then 42
      else if column = 80 then 4194304 * 129 * 943718400
      else 0
    else
      if column = 11 then 1
      else if column = 34 then 5
      else if column = 40 then 8
      else if column = 46 then 9
      else 0
  else if stage = 2 then
    if column = 34 then if kind.val = 1 then 9 else 6
    else if column = 40 then if kind.val = 2 then 10 else 5
    else gapAssignment (memoryGapNegative kind) stage column
  else gapAssignment (memoryGapNegative kind) stage column
private def memoryGapRow (kind : Fin 3) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, memoryGapAssignment kind stage⟩
private def memoryGapCells : List Cell := [.register 0, .register 10, .register 12, .ram 4194304]
private def memoryGapData (kind : Fin 3) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData (memoryGapNegative kind) with machine := { (chainData (memoryGapNegative kind)).machine with
      rows := [memoryGapRow kind 2, memoryGapRow kind 1, memoryGapRow kind 0]
      rom := UnifiedReduced.Setup.table (memoryGapBefore kind)
      terminal := (memoryGapRow kind 2).finish
      initialMemory := [(Cell.register 0).initialToken 0, (Cell.register 10).initialToken 4194304,
        (Cell.register 12).initialToken 65537, (Cell.ram 4194304).initialToken 42]
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (if kind.val = 0 then 10 else if kind.val = 1 then 8 else 0, 0),
          Nat.pair (if kind.val = 0 then 42 else 0) (if kind.val = 0 then 0 else 64)⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩,
        ⟨(Cell.ram 4194304).addressCode, (if kind.val = 0 then 9 else if kind.val = 1 then 10 else 0, 0),
          Nat.pair (if kind.val = 1 then 129 else 42) 0⟩] } }

private theorem memoryGapCore (kind : Fin 3) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (memoryGapAssignment kind stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (memoryGapBefore kind))) := by
  fin_cases kind <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, memoryGapAssignment, gapAssignment, memoryGapNegative, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains; decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun n : Nat => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem memoryGapClocks (kind : Fin 3) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (memoryGapAssignment kind stage)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases kind <;> fin_cases stage <;> decide +kernel

private theorem memoryGapAccepted (kind : Fin 3) :
    UnifiedReduced.Caller.MixedMemoryAccepted (memoryGapData kind) (memoryGapProgram kind) := by
  constructor
  · constructor
    · intro current member
      have rows : current = memoryGapRow kind 2 ∨ current = memoryGapRow kind 1 ∨ current = memoryGapRow kind 0 := by
        simpa [memoryGapData, chainData] using member
      rcases rows with rfl | rfl | rfl
      · exact Verification.holds_append (memoryGapCore kind 2) (memoryGapClocks kind 2)
      · exact Verification.holds_append (memoryGapCore kind 1) (memoryGapClocks kind 1)
      · exact Verification.holds_append (memoryGapCore kind 0) (memoryGapClocks kind 0)
    · intro current member
      have rows : current = memoryGapRow kind 2 ∨ current = memoryGapRow kind 1 ∨ current = memoryGapRow kind 0 := by
        simpa [memoryGapData, chainData] using member
      rcases rows with rfl | rfl | rfl <;> fin_cases kind <;> decide +kernel
    · change [(memoryGapRow kind 0).start, (memoryGapRow kind 2).finish,
          (memoryGapRow kind 1).finish, (memoryGapRow kind 0).finish].Perm
        [(memoryGapRow kind 2).finish, (memoryGapRow kind 2).start,
          (memoryGapRow kind 1).start, (memoryGapRow kind 0).start]
      have first : (memoryGapRow kind 0).finish = (memoryGapRow kind 1).start := by fin_cases kind <;> rfl
      have second : (memoryGapRow kind 1).finish = (memoryGapRow kind 2).start := by fin_cases kind <;> rfl
      rw [first, second]
      exact (List.Perm.swap _ _ _).trans ((List.Perm.cons _ (List.Perm.swap _ _ _)).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ []))))
    · intro current member
      have empty : (memoryGapData kind).callers = [] := by fin_cases kind <;> decide +kernel
      rw [empty] at member
      cases member
    · intro current member
      cases member
    · intro current member
      cases member
    · have empty : (memoryGapData kind).calls = [] := by fin_cases kind <;> decide +kernel
      rw [empty]
      exact List.Perm.refl []
  · intro current member _
    have rows : current = memoryGapRow kind 2 ∨ current = memoryGapRow kind 1 ∨ current = memoryGapRow kind 0 := by
      simpa [memoryGapData, chainData] using member
    rcases rows with rfl | rfl | rfl
    · exact ⟨(2 : Fin 3), by fin_cases kind <;> decide +kernel⟩
    · exact ⟨(1 : Fin 3), by fin_cases kind <;> decide +kernel⟩
    · exact ⟨(0 : Fin 3), by fin_cases kind <;> decide +kernel⟩
  · fin_cases kind <;> decide +kernel

private theorem memoryGapImage (kind : Fin 3) :
    UnifiedReduced.Mixed.programImage (memoryGapBefore kind) [0, 4, 8] = some (memoryGapProgram kind) := by
  have first : (Cell.ram 0).read (memoryGapBefore kind) = .ok (dataflowSeedBits (memoryGapNegative kind)) (memoryGapBefore kind) :=
    written_word_disjoint 8 (memoryGapLastBits kind) (by decide)
      (written_word_disjoint 4 (memoryGapBits kind) (by decide) (written_word_read (wordWriteState memoryGapBase 4194304 42) 0 (dataflowSeedBits (memoryGapNegative kind))))
  have second : (Cell.ram 4).read (memoryGapBefore kind) = .ok (memoryGapBits kind) (memoryGapBefore kind) :=
    written_word_disjoint 8 (memoryGapLastBits kind) (by decide) (written_word_read _ 4 (memoryGapBits kind))
  have third : (Cell.ram 8).read (memoryGapBefore kind) = .ok (memoryGapLastBits kind) (memoryGapBefore kind) := written_word_read _ 8 _
  have decodeFirst : run (SailRV32.Functions.encdec_backwards (dataflowSeedBits (memoryGapNegative kind))) (memoryGapBefore kind) =
      .ok (dataflowSeedEntry (memoryGapNegative kind)).instruction (memoryGapBefore kind) := by fin_cases kind <;> with_unfolding_all rfl
  have decodeSecond : run (SailRV32.Functions.encdec_backwards (memoryGapBits kind)) (memoryGapBefore kind) =
      .ok (memoryGapMiddleEntry kind).instruction (memoryGapBefore kind) := by fin_cases kind <;> with_unfolding_all rfl
  have decodeThird : run (SailRV32.Functions.encdec_backwards (memoryGapLastBits kind)) (memoryGapBefore kind) =
      .ok (memoryGapLastEntry kind).instruction (memoryGapBefore kind) := by fin_cases kind <;> with_unfolding_all rfl
  have fieldsFirst : UnifiedReduced.Mixed.decoderFields (dataflowSeedEntry (memoryGapNegative kind)).instruction =
      some (dataflowSeedEntry (memoryGapNegative kind)).data := by fin_cases kind <;> with_unfolding_all rfl
  have fieldsSecond : UnifiedReduced.Mixed.decoderFields (memoryGapMiddleEntry kind).instruction =
      some (memoryGapMiddleEntry kind).data := by fin_cases kind <;> with_unfolding_all rfl
  have fieldsThird : UnifiedReduced.Mixed.decoderFields (memoryGapLastEntry kind).instruction = some (memoryGapLastEntry kind).data := by fin_cases kind <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, first, second, third, decodeFirst, decodeSecond, decodeThird,
    fieldsFirst, fieldsSecond, fieldsThird, bind, Option.bind, pure]
  fin_cases kind <;> rfl

private theorem memoryGapInputs (kind : Fin 3) : UnifiedReduced.Caller.MixedMemoryInputs
    (memoryGapData kind) (memoryGapProgram kind) (memoryGapBefore kind) [] [0, 4, 8] memoryGapCells := by
  refine ⟨⟨rfl, ?_, by fin_cases kind <;> decide +kernel⟩, memoryGapImage kind, ?_, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · have zero : (Cell.register 0).read (memoryGapBefore kind) = .ok 0 (memoryGapBefore kind) := by with_unfolding_all rfl
    have ten : (Cell.register 10).read (memoryGapBefore kind) = .ok 4194304 (memoryGapBefore kind) := by
      apply read_register
      simp [memoryGapBefore, wordWriteState, memoryGapBase, initialState]
    have twelve : (Cell.register 12).read (memoryGapBefore kind) = .ok 65537 (memoryGapBefore kind) := by
      apply read_register
      simp [memoryGapBefore, wordWriteState, memoryGapBase, initialState, Std.ExtDHashMap.get?_insert]
    have ram : (Cell.ram 4194304).read (memoryGapBefore kind) = .ok 42 (memoryGapBefore kind) :=
      written_word_disjoint 8 (memoryGapLastBits kind) (by decide)
        (written_word_disjoint 4 (memoryGapBits kind) (by decide)
          (written_word_disjoint 0 (dataflowSeedBits (memoryGapNegative kind)) (by decide)
            (written_word_read memoryGapBase 4194304 42)))
    simp only [initialImage, memoryGapCells, zero, ten, twelve, ram, List.mapM_cons, List.mapM_nil, bind, pure]
    rfl
  · intro cell member
    have choices : cell = .register 0 ∨ cell = .register 10 ∨ cell = .register 12 ∨ cell = .ram 4194304 := by
      simpa [memoryGapCells] using member
    rcases choices with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned]
  · intro current member
    cases member

private theorem memoryGapRegistry (kind : Fin 3) : UnifiedReduced.Caller.WrappedSequentialProgram (memoryGapProgram kind) := by
  constructor
  · intro current member
    have entries : current = dataflowSeedEntry (memoryGapNegative kind) ∨ current = memoryGapMiddleEntry kind ∨ current = memoryGapLastEntry kind := by
      simpa [memoryGapProgram] using member
    rcases entries with rfl | rfl | rfl
    · exact .sequential (.arithmetic (.addi _ _ _))
    · fin_cases kind
      · exact .sequential (.lw _ _ _)
      · exact .sequential (.sw _ _ _)
      · exact .sequential (.lw _ _ _)
    · exact .sequential (.arithmetic (.addi _ _ _))
  · intro current member
    have entries : current = dataflowSeedEntry (memoryGapNegative kind) ∨ current = memoryGapMiddleEntry kind ∨ current = memoryGapLastEntry kind := by
      simpa [memoryGapProgram] using member
    rcases entries with rfl | rfl | rfl <;> fin_cases kind <;> decide

private theorem memoryGapSeedScope (kind : Fin 3) : UnifiedReduced.Caller.ControlPreparation
    (memoryGapData kind) (memoryGapProgram kind) 8 12 (.addi (dataflowSeed (memoryGapNegative kind))) := by
  refine ⟨.wrappedSequential (by decide) (memoryGapBefore kind) rfl (memoryGapRegistry kind) ?_, rfl,
    by fin_cases kind <;> decide +kernel, by fin_cases kind <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry (memoryGapNegative kind) ∨ current = memoryGapMiddleEntry kind ∨ current = memoryGapLastEntry kind := by
    simpa [memoryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · rfl
  · rw [memoryGapMiddlePC] at address
    change (4 : BitVec 32) = 0 at address
    contradiction
  · change (8 : BitVec 32) = 0 at address
    contradiction

private theorem memoryGapLoadScope (kind : Fin 3) (notStore : kind.val ≠ 1) : UnifiedReduced.Caller.LoadFramePreparation
    (memoryGapData kind) (memoryGapProgram kind) 12 (if kind.val = 0 then 10 else 12)
      (if kind.val = 0 then 10 else 0) (if kind.val = 0 then 0 else 2) := by
  refine ⟨memoryGapRegistry kind, ?_, rfl, by fin_cases kind <;> decide +kernel, by fin_cases kind <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry (memoryGapNegative kind) ∨ current = memoryGapMiddleEntry kind ∨ current = memoryGapLastEntry kind := by
    simpa [memoryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · fin_cases kind <;> simp_all [memoryGapMiddleEntry]
  · change (8 : BitVec 32) = 4 at address
    contradiction


private theorem memoryGapStoreScope : UnifiedReduced.Caller.StoreFramePreparation
    (memoryGapData 1) (memoryGapProgram 1) 12 10 12 0 := by
  refine ⟨memoryGapRegistry (1 : Fin 3), ?_, rfl, by decide +kernel, by decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry (memoryGapNegative (1 : Fin 3)) ∨ current = memoryGapMiddleEntry (1 : Fin 3) ∨ current = memoryGapLastEntry (1 : Fin 3) := by
    simpa [memoryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 4 at address
    contradiction
  · rfl
  · change (8 : BitVec 32) = 4 at address
    contradiction


private theorem memoryGapLastScope (kind : Fin 3) : UnifiedReduced.Caller.RegisterImmediatePreparation
    (memoryGapData kind) (memoryGapProgram kind) 16 12 12 (dataflowImmediate (memoryGapNegative kind)) := by
  refine ⟨memoryGapRegistry kind, ?_, rfl, by fin_cases kind <;> decide +kernel, by fin_cases kind <;> decide +kernel⟩
  intro current member address
  have entries : current = dataflowSeedEntry (memoryGapNegative kind) ∨ current = memoryGapMiddleEntry kind ∨ current = memoryGapLastEntry kind := by
    simpa [memoryGapProgram] using member
  rcases entries with rfl | rfl | rfl
  · change (0 : BitVec 32) = 8 at address
    contradiction
  · rw [memoryGapMiddlePC] at address
    change (4 : BitVec 32) = 8 at address
    contradiction
  · rfl


private def memoryGapValue (kind : Fin 3) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed (memoryGapNegative kind))).value
private theorem memoryGapFramed (kind : Fin 3) : UnifiedReduced.Caller.PublicRegisterDataflow
    (memoryGapData kind) (memoryGapProgram kind) 12 12 (memoryGapValue kind) := by
  fin_cases kind
  · exact .loadFrame (.prepared (.literal (memoryGapSeedScope 0))) (memoryGapLoadScope 0 (by decide)) (by decide)
  · exact .storeFrame (.prepared (.literal (memoryGapSeedScope 1))) memoryGapStoreScope
  · exact .loadFrame (.prepared (.literal (memoryGapSeedScope 2))) (memoryGapLoadScope 2 (by decide)) (by decide)
private theorem memoryGapPreparation (kind : Fin 3) : UnifiedReduced.Caller.PublicRegisterDataflow
    (memoryGapData kind) (memoryGapProgram kind) 16 12
      (UnifiedReduced.Caller.registerImmediateValue (memoryGapValue kind) (dataflowImmediate (memoryGapNegative kind))) :=
  .addi (memoryGapFramed kind) (memoryGapLastScope kind) (by decide)

theorem public_memory_gap_gap_preparation (kind : Fin 3) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (memoryGapData kind) (memoryGapBefore kind) memoryGapCells 12 12 (memoryGapValue kind) :=
  UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (memoryGapAccepted kind) (memoryGapInputs kind) (memoryGapFramed kind) (by decide) (by decide)

theorem public_memory_gap_final_preparation (kind : Fin 3) : UnifiedReduced.Caller.RegisterDataflowBoundaryExecution
    (memoryGapData kind) (memoryGapBefore kind) memoryGapCells 16 12 128 := by
  have result := UnifiedReduced.Caller.register_dataflow_control_preparation_soundness (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (memoryGapAccepted kind) (memoryGapInputs kind) (memoryGapPreparation kind) (by decide) (by decide)
  have value : UnifiedReduced.Caller.registerImmediateValue (memoryGapValue kind) (dataflowImmediate (memoryGapNegative kind)) = 128 := by
    fin_cases kind <;> decide +kernel
  exact value ▸ result

theorem public_memory_gap_protocol_source (kind : Fin 3) : UnifiedReduced.Caller.HashControlPreparation
    (memoryGapData kind) (memoryGapProgram kind) 16 (.blakeG true) :=
  UnifiedReduced.Caller.Proofs.register_dataflow_hash_preparation_source (memoryGapInputs kind).initialization
    (memoryGapInputs kind).distinct (memoryGapFramed kind) (memoryGapLastScope kind) (by decide)
    (by fin_cases kind <;> decide +kernel)

theorem public_memory_gap_protocol_preparation (kind : Fin 3) : UnifiedReduced.Caller.PreparedBoundaryExecution
    (memoryGapData kind) (memoryGapBefore kind) memoryGapCells 16 12 (UnifiedReduced.Caller.hashPreparation (.blakeG true)) :=
  UnifiedReduced.Caller.register_dataflow_hash_preparation_soundness (span := .blakeG true) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (memoryGapAccepted kind) (memoryGapInputs kind) (memoryGapFramed kind) (memoryGapLastScope kind)
    (by decide) (by fin_cases kind <;> decide +kernel) (by decide)

theorem public_memory_gap_actual_final_cycle (kind : Fin 3) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atSource atCut : State),
      events.Perm (((memoryGapData kind).prefixSteps 12).map transferEvent) ∧
      SailHistory memoryGapCells events (memoryGapBefore kind) atSource ∧
      SailHistory memoryGapCells (rowEvents 1 (memoryGapRow kind 2)).reverse atSource atCut ∧
      (Cell.register 12).read atSource = .ok (memoryGapValue kind) atSource ∧
      (Cell.register 12).read atCut = .ok 128 atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = 14 ∧ token.word = Word.ofBitVec 128 := by
  obtain ⟨row, member, last, tokens, events, atSource, atCut, permutation, past, native, _,
    value, read, written, token, present, address, time, word⟩ :=
    UnifiedReduced.Caller.register_immediate_control_preparation_soundness (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (memoryGapAccepted kind) (memoryGapInputs kind) (memoryGapLastScope kind) (by decide) (by decide)
  have same : row = memoryGapRow kind 2 := by
    have choices : row = memoryGapRow kind 2 ∨ row = memoryGapRow kind 1 ∨ row = memoryGapRow kind 0 := by
      simpa [memoryGapData] using member
    rcases choices with same | rfl | rfl
    · exact same
    · have impossible : 12 = 16 := by fin_cases kind <;> exact last
      omega
    · have impossible : 8 = 16 := by fin_cases kind <;> exact last
      omega
  subst row
  have actual := Trace.Proofs.native_history_read (columns := UnifiedReduced.importedConstraintsTraceColumns)
    (ports := UnifiedReduced.importedConstraintsMemoryPorts) (w := memoryGapAssignment kind 2)
    (port := UnifiedReduced.importedConstraintsMemoryPorts[0]) (cell := Cell.register 12) 1 rfl rfl rfl native
    (by simp [UnifiedReduced.importedConstraintsMemoryPorts]) (by fin_cases kind <;> decide +kernel)
  have operand : memoryWord (UnifiedReduced.importedConstraintsMemoryPorts[0].readCode (memoryGapAssignment kind 2)) = memoryGapValue kind := by
    fin_cases kind <;> decide +kernel
  rw [operand] at actual
  have equal : value = memoryGapValue kind := (EStateM.Result.ok.inj (read.symm.trans actual)).1
  subst value
  have result : UnifiedReduced.Caller.registerImmediateValue (memoryGapValue kind) (dataflowImmediate (memoryGapNegative kind)) = 128 := by
    fin_cases kind <;> decide +kernel
  exact ⟨tokens, events, atSource, atCut, permutation, past, native, actual, result ▸ written,
    token, present, address, time, result ▸ word⟩

theorem public_memory_gap_wrong_value_rejected (kind : Fin 3) :
    UnifiedReduced.Caller.registerImmediateValue (memoryGapValue kind) (dataflowImmediate (memoryGapNegative kind)) ≠
      (Delegation.Caller.HashSpan.blakeG false).controlStart := by fin_cases kind <;> decide +kernel

theorem public_memory_gap_incomplete_reference_rejected (kind : Fin 3) :
    ¬ UnifiedReduced.Caller.ComputedProtocolWindowInputs (memoryGapData kind) (memoryGapProgram kind) ⟨.blakeG true, 16, 16⟩ := by
  intro scope
  have count := scope.calls
  change 0 = 56 at count
  contradiction


theorem public_memory_gap_retains_register_and_ram (kind : Fin 3) :
    ∃ (tokens : List (MemoryToken babyBearModulus)) (events : List MemoryAccess) (atGap : State),
      events.Perm (((memoryGapData kind).prefixSteps 12).map transferEvent) ∧
      SailHistory memoryGapCells events (memoryGapBefore kind) atGap ∧
      ((memoryGapData kind).machine.initialMemory ++ ((memoryGapData kind).prefixSteps 12).map Prod.snd).Perm
        (tokens ++ ((memoryGapData kind).prefixSteps 12).map Prod.fst) ∧
      (Cell.register 12).read atGap = .ok (memoryGapValue kind) atGap ∧
      (Cell.register 10).read atGap = .ok (if kind.val = 0 then 42 else 4194304) atGap ∧
      (Cell.ram 4194304).read atGap = .ok (if kind.val = 1 then 129 else 42) atGap ∧
      (∃ token ∈ tokens, token.address = (Cell.register 12).addressCode ∧
        (timeOfPair token.time).value = (if kind.val = 1 then 9 else 6) ∧ token.word = Word.ofBitVec (memoryGapValue kind)) ∧
      ∃ token ∈ tokens, token.address = (Cell.ram 4194304).addressCode ∧
        (timeOfPair token.time).value = (if kind.val = 0 then 9 else if kind.val = 1 then 10 else 0) ∧
        token.word = Word.ofBitVec (if kind.val = 1 then 129 else 42) := by
  obtain ⟨tokens, _, events, _, atGap, _, permutation, _, history, _, matching, _, boundary, _⟩ :=
    (UnifiedReduced.Caller.Proofs.mixed_window_execution (lower := 12) (upper := 12)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (memoryGapAccepted kind) (memoryGapInputs kind)
      (by decide) (by decide) (by decide) (by decide)).execution
  let tracked : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode,
    (if kind.val = 1 then 9 else 6, 0), Nat.pair (if kind.val = 1 then 129 else 127) 0⟩
  let other : MemoryToken babyBearModulus := ⟨(Cell.register 10).addressCode,
    (if kind.val = 0 then 10 else if kind.val = 1 then 8 else 0, 0),
    Nat.pair (if kind.val = 0 then 42 else 0) (if kind.val = 0 then 0 else 64)⟩
  let ram : MemoryToken babyBearModulus := ⟨(Cell.ram 4194304).addressCode,
    (if kind.val = 0 then 9 else if kind.val = 1 then 10 else 0, 0), Nat.pair (if kind.val = 1 then 129 else 42) 0⟩
  have actual (token : MemoryToken babyBearModulus)
      (produced : token ∈ (memoryGapData kind).machine.initialMemory ++ ((memoryGapData kind).prefixSteps 12).map Prod.snd)
      (notRead : token ∉ ((memoryGapData kind).prefixSteps 12).map Prod.fst) : token ∈ tokens := by
    rcases List.mem_append.mp (matching.mem_iff.mp produced) with present | read
    · exact present
    · exact False.elim (notRead read)
  have trackedPresent : tracked ∈ tokens := actual tracked (by fin_cases kind <;> decide +kernel) (by fin_cases kind <;> decide +kernel)
  have otherPresent : other ∈ tokens := actual other (by fin_cases kind <;> decide +kernel) (by fin_cases kind <;> decide +kernel)
  have ramPresent : ram ∈ tokens := actual ram (by fin_cases kind <;> decide +kernel) (by fin_cases kind <;> decide +kernel)
  obtain ⟨cell, _, code, read⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary trackedPresent
  have same : cell = Cell.register 12 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, otherRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary otherPresent
  have same : cell = Cell.register 10 := Trace.Proofs.cell_address_injective code
  subst cell
  obtain ⟨cell, _, code, ramRead⟩ := UnifiedReduced.Caller.Proofs.native_boundary_read boundary ramPresent
  have same : cell = Cell.ram 4194304 := Trace.Proofs.cell_address_injective code
  subst cell
  have trackedWord : tracked.word = Word.ofBitVec (memoryGapValue kind) := by fin_cases kind <;> decide +kernel
  have otherWord : other.word = Word.ofBitVec (if kind.val = 0 then 42 else 4194304) := by fin_cases kind <;> decide +kernel
  have ramWord : ram.word = Word.ofBitVec (if kind.val = 1 then 129 else 42) := by fin_cases kind <;> decide +kernel
  rw [trackedWord, Word.ofBitVec_roundtrip] at read
  rw [otherWord, Word.ofBitVec_roundtrip] at otherRead
  rw [ramWord, Word.ofBitVec_roundtrip] at ramRead
  exact ⟨tokens, events, atGap, permutation, history, matching, read, otherRead, ramRead,
    ⟨tracked, trackedPresent, rfl, by fin_cases kind <;> decide, trackedWord⟩,
    ram, ramPresent, rfl, by fin_cases kind <;> decide, ramWord⟩

theorem public_memory_gap_discarded_load_retained :
    UnifiedReduced.Caller.PublicRegisterDataflow (memoryGapData 2) (memoryGapProgram 2) 12 12 127 ∧
      ¬ NoDiscardedLoads (memoryGapProgram 2) ∧
      (127 + 2 : BitVec 32).toNat % 4 ≠ 0 ∧
      ∀ edge ∈ (memoryGapData 2).windowSteps 8 12,
        edge.1.address = (Cell.register 0).addressCode ∧ edge.2.address = (Cell.register 0).addressCode := by
  refine ⟨memoryGapFramed 2, ?_, by decide, by decide +kernel⟩
  intro excluded
  exact excluded (memoryGapMiddleEntry 2) (by simp [memoryGapProgram]) 2 12 rfl

theorem public_memory_gap_wrong_load_destination_rejected :
    ¬ UnifiedReduced.Caller.LoadFramePreparation (memoryGapData 0) (memoryGapProgram 0) 12 10 12 0 := by
  intro scope
  have instruction := scope.atCut (memoryGapMiddleEntry 0) (by simp [memoryGapProgram]) (by decide +kernel)
  have destination := congrArg (fun args => args.2.2.1) (SailRV32.instruction.LOAD.inj instruction)
  exact (by decide : (10 : BitVec 5) ≠ 12) (SailRV32.regidx.Regidx.inj destination)

theorem public_memory_gap_wrong_store_source_rejected :
    ¬ UnifiedReduced.Caller.StoreFramePreparation (memoryGapData 1) (memoryGapProgram 1) 12 12 12 0 := by
  intro scope
  have instruction := scope.atCut (memoryGapMiddleEntry 1) (by simp [memoryGapProgram]) (by decide +kernel)
  have source := congrArg (fun args => args.2.2.1) (SailRV32.instruction.STORE.inj instruction)
  exact (by decide : (10 : BitVec 5) ≠ 12) (SailRV32.regidx.Regidx.inj source)

private def forgedMemoryGapData (kind : Fin 3) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { memoryGapData kind with machine := { (memoryGapData kind).machine with
      rows := [⟨.machine, fun column => if column = 34 then 10 else memoryGapAssignment kind 2 column⟩,
        memoryGapRow kind 1, memoryGapRow kind 0] } }

theorem public_memory_gap_fabricated_fresh_source_rejected (kind : Fin 3) :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted (forgedMemoryGapData kind) (memoryGapProgram kind) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (10, 0), Nat.pair (if kind.val = 1 then 129 else 127) 0⟩
  have member : token ∈ (forgedMemoryGapData kind).mixedSteps.map Prod.fst := by fin_cases kind <;> decide +kernel
  have absent : token ∉ (forgedMemoryGapData kind).machine.initialMemory ++ (forgedMemoryGapData kind).mixedSteps.map Prod.snd := by
    fin_cases kind <;> decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

theorem public_memory_gap_fabricated_fresh_source_native (kind : Fin 3) :
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 34 then 10 else memoryGapAssignment kind 2 column))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (memoryGapBefore kind)) ++
        UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · fin_cases kind
    all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Verification.environment, Expression.eval, memoryGapAssignment, gapAssignment, memoryGapNegative, chainAssignment, assignment, register,
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
      all_goals fin_cases kind <;> decide +kernel

private def forgedMemoryLoadAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 42 || column = 50 then 43
  else if column = 80 then 4194304 * 43 * 943718400
  else memoryGapAssignment 0 1 column
private def forgedMemoryLoadData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { memoryGapData 0 with machine := { (memoryGapData 0).machine with
      rows := [memoryGapRow 0 2, ⟨.machine, forgedMemoryLoadAssignment⟩, memoryGapRow 0 0] } }

theorem public_memory_gap_fabricated_ram_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedMemoryLoadData (memoryGapProgram 0) := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.ram 4194304).addressCode, (0, 0), Nat.pair 43 0⟩
  have member : token ∈ forgedMemoryLoadData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedMemoryLoadData.machine.initialMemory ++ forgedMemoryLoadData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

theorem public_memory_gap_fabricated_ram_read_native : FlatOperation.ConstraintsHoldFlat
    (Verification.environment forgedMemoryLoadAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (memoryGapBefore 0)) ++
      UnifiedReduced.importedConstraintsTimestampLookups) := by
  apply Verification.holds_append
  · simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat, Verification.environment,
      Expression.eval, forgedMemoryLoadAssignment, memoryGapAssignment, Lookup.Contains, Table.toRaw, fromElements]
    repeat' apply And.intro
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
      all_goals decide +kernel


end Tests.ControlPreparation
