import Tests.ControlPreparationBinaryGap

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def comparisonCustomGapBits (negative : Bool) : BitVec 32 := if negative then 0xc2c64573 else 0x00c63533
def comparisonCustomGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
def comparisonCustomGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (comparisonCustomGapBits negative)) 8 (comparisonCustomGapLastBits negative)
def comparisonCustomGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, comparisonCustomGapBits negative,
    if negative then .ZIMOP_MOP_RR (4, .Regidx 12, .Regidx 12, .Regidx 10)
    else .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, .SLTU),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, if negative then 512 else 4096, if negative then 0 else 3⟩⟩
def comparisonCustomGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, comparisonCustomGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def comparisonCustomGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, comparisonCustomGapMiddleEntry negative, comparisonCustomGapLastEntry negative]
def comparisonCustomGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
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
def comparisonCustomGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, comparisonCustomGapAssignment negative stage⟩
def comparisonCustomGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [comparisonCustomGapRow negative 2, comparisonCustomGapRow negative 1, comparisonCustomGapRow negative 0]
      rom := UnifiedReduced.Setup.table (comparisonCustomGapBefore negative)
      terminal := (comparisonCustomGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 259 else 0) (if negative then 1 else 0)⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

theorem comparisonCustomGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (comparisonCustomGapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (comparisonCustomGapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, comparisonCustomGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | (with_unfolding_all refine ⟨⟨524545, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨655617, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | (with_unfolding_all refine ⟨⟨786745, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
        UnifiedReduced.Setup.conditionalKey, Verification.conditionalValue])
    | (with_unfolding_all refine ⟨⟨721161, by decide⟩, ?_⟩; dsimp only; rw [UnifiedReduced.Setup.Proofs.row_eq_reference]; norm_num [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow])
    | decide +kernel

theorem comparisonCustomGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem comparisonCustomGapAccepted (negative : Bool) :
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

theorem comparisonCustomGapImage (negative : Bool) :
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

theorem comparisonCustomGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem comparisonCustomGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (comparisonCustomGapProgram negative) := by
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

theorem comparisonCustomGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
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

theorem comparisonCustomGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterFramePreparation
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

theorem comparisonCustomGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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


def comparisonCustomGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
theorem comparisonCustomGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (comparisonCustomGapData negative) (comparisonCustomGapProgram negative) 12 12 (comparisonCustomGapValue negative) :=
  .registerFrame (.prepared (.literal (comparisonCustomGapSeedScope negative))) (comparisonCustomGapMiddleScope negative) (by decide) (by decide)
theorem comparisonCustomGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
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


def staleComparisonCustomGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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
      | (apply Verification.range16_contains; decide +kernel)
      | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
         dsimp only
         rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
         simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
           UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
         with_unfolding_all decide +kernel)
      | decide +kernel

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


def memoryGapNegative (kind : Fin 3) : Bool := kind.val == 1

end Tests.ControlPreparation
