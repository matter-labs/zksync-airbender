import Tests.ControlPreparationGapFixtures

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def arithmeticGapBits (negative : Bool) : BitVec 32 := if negative then 0x40c60533 else 0x00c60533
def arithmeticGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
def arithmeticGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (arithmeticGapBits negative)) 8 (arithmeticGapLastBits negative)
def arithmeticGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, arithmeticGapBits negative, .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, if negative then .SUB else .ADD),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, if negative then 2 else 1, 0⟩⟩
def arithmeticGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, arithmeticGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def arithmeticGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, arithmeticGapMiddleEntry negative, arithmeticGapLastEntry negative]
def arithmeticGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
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
def arithmeticGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, arithmeticGapAssignment negative stage⟩
def arithmeticGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [arithmeticGapRow negative 2, arithmeticGapRow negative 1, arithmeticGapRow negative 0]
      rom := UnifiedReduced.Setup.table (arithmeticGapBefore negative)
      terminal := (arithmeticGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 0 else 254) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

theorem arithmeticGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem arithmeticGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem arithmeticGapAccepted (negative : Bool) :
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

theorem arithmeticGapImage (negative : Bool) :
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

theorem arithmeticGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem arithmeticGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (arithmeticGapProgram negative) := by
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

theorem arithmeticGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
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

theorem arithmeticGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.ArithmeticFramePreparation
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

theorem arithmeticGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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


def arithmeticGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
theorem arithmeticGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (arithmeticGapData negative) (arithmeticGapProgram negative) 12 12 (arithmeticGapValue negative) :=
  .arithmeticFrame (.prepared (.literal (arithmeticGapSeedScope negative))) (arithmeticGapMiddleScope negative) (by decide) (by decide)
theorem arithmeticGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
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


def staleArithmeticGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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


end Tests.ControlPreparation
