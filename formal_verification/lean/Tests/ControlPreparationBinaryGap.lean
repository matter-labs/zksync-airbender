import Tests.ControlPreparationChains

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def binaryGapBits (negative : Bool) : BitVec 32 := if negative then 0x00c67533 else 0x00c64533
def binaryGapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
def binaryGapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (binaryGapBits negative)) 8 (binaryGapLastBits negative)
def binaryGapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, binaryGapBits negative, .RTYPE (.Regidx 12, .Regidx 12, .Regidx 10, if negative then .AND else .XOR),
    ⟨.machine, 12, 12, 10, ⟨0, 0⟩, 65536, if negative then 54 else 52⟩⟩
def binaryGapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, binaryGapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def binaryGapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, binaryGapMiddleEntry negative, binaryGapLastEntry negative]
def binaryGapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
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
def binaryGapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, binaryGapAssignment negative stage⟩
def binaryGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [binaryGapRow negative 2, binaryGapRow negative 1, binaryGapRow negative 0]
      rom := UnifiedReduced.Setup.table (binaryGapBefore negative)
      terminal := (binaryGapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 0) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

private theorem binaryGapMember (initial : State) (index : Fin 524545)
    (value : Vector (ZMod babyBearModulus) 10)
    (equal : value = ((Verification.referenceShiftBinopRow index).set 9
      (UnifiedReduced.Setup.binaryTag (Verification.referenceShiftBinopRow index)[9])).map
        (fun n : Nat => (n : ZMod babyBearModulus))) :
    (UnifiedReduced.Setup.table initial).Contains #[] value := by
  change ∃ i : Fin 2097537, _
  refine ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  dsimp only
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
  have fixedBound : index.val < 1048961 := by have := index.isLt; omega
  simpa only [UnifiedReduced.Setup.referenceRow, dif_pos fixedBound,
    UnifiedReduced.Setup.referenceFixedRow, dif_pos index.isLt,
    UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference] using equal

theorem binaryGapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (binaryGapAssignment negative stage))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (binaryGapBefore negative))) := by
  cases negative <;> fin_cases stage
  all_goals simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, binaryGapAssignment, arithmeticGapAssignment, gapAssignment, chainAssignment, dataflowAssignment, assignment, register,
    Lookup.Contains, Table.toRaw, fromElements]
  all_goals repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (apply binaryGapMember _ (⟨0, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply binaryGapMember _ (⟨1, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply binaryGapMember _ (⟨257, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply binaryGapMember _ (⟨257 + 127 * 256 + 127, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply binaryGapMember _ (⟨131329, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | (apply binaryGapMember _ (⟨131329 + 129 * 256 + 129, by decide⟩ : Fin 524545); with_unfolding_all decide +kernel)
    | decide +kernel

theorem binaryGapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem binaryGapAccepted (negative : Bool) :
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

theorem binaryGapImage (negative : Bool) :
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

theorem binaryGapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem binaryGapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (binaryGapProgram negative) := by
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

theorem binaryGapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
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

theorem binaryGapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterFramePreparation
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

theorem binaryGapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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


def binaryGapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
theorem binaryGapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (binaryGapData negative) (binaryGapProgram negative) 12 12 (binaryGapValue negative) :=
  .registerFrame (.prepared (.literal (binaryGapSeedScope negative))) (binaryGapMiddleScope negative) (by decide) (by decide)
theorem binaryGapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
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


def staleBinaryGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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



end Tests.ControlPreparation
