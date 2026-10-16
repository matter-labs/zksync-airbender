import Tests.ControlPreparationValues

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def chainBits (negative : Bool) : BitVec 32 := if negative then 0xfff60513 else 0x00160513
def chainBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (chainBits negative)) 8 0x00050613
def chainMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, chainBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 10, .ADDI),
    ⟨.machine, 12, 0, 10, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def chainLastEntry : UnifiedReduced.ProgramEntry :=
  ⟨8, 0x00050613, .ITYPE (0, .Regidx 10, .Regidx 12, .ADDI), ⟨.machine, 10, 0, 12, ⟨0, 0⟩, 1, 0⟩⟩
def chainProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, chainMiddleEntry negative, chainLastEntry]
def chainCells : List Cell := [.register 0, .register 10, .register 12]
def chainAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
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
def chainRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, chainAssignment negative stage⟩
def chainData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [chainRow negative 2, chainRow negative 1, chainRow negative 0]
      rom := UnifiedReduced.Setup.table (chainBefore negative)
      terminal := (chainRow negative 2).finish
      initialMemory := [(Cell.register 0).initialToken 0, (Cell.register 10).initialToken 65537, (Cell.register 12).initialToken 65537]
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (12, 0), Nat.pair 128 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

theorem chainCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem chainClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem chainAccepted (negative : Bool) :
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

theorem chainImage (negative : Bool) :
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

theorem chainInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem chainRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (chainProgram negative) := by
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

theorem chainSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
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

theorem chainMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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

theorem chainLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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

def chainValue (negative : Bool) : BitVec 32 := UnifiedReduced.Caller.registerImmediateValue
  (UnifiedReduced.Caller.registerImmediateValue (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
    (dataflowImmediate negative)) 0
theorem chainPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterPreparation
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

def forgedChainData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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

def gapBits (_negative : Bool) : BitVec 32 := 0x00060513
def gapLastBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
def gapBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (gapBits negative)) 8 (gapLastBits negative)
def gapMiddleEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, gapBits negative, .ITYPE (0, .Regidx 12, .Regidx 10, .ADDI), ⟨.machine, 12, 0, 10, ⟨0, 0⟩, 1, 0⟩⟩
def gapLastEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨8, gapLastBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def gapProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, gapMiddleEntry negative, gapLastEntry negative]
def gapAssignment (negative : Bool) (stage : Fin 3) (column : Nat) : ZMod babyBearModulus :=
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
def gapRow (negative : Bool) (stage : Fin 3) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, gapAssignment negative stage⟩
def gapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { chainData negative with machine := { (chainData negative).machine with
      rows := [gapRow negative 2, gapRow negative 1, gapRow negative 0]
      rom := UnifiedReduced.Setup.table (gapBefore negative)
      terminal := (gapRow negative 2).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (13, 0), 0⟩,
        ⟨(Cell.register 10).addressCode, (10, 0), Nat.pair (if negative then 129 else 127) 0⟩,
        ⟨(Cell.register 12).addressCode, (14, 0), Nat.pair 128 0⟩] } }

theorem gapCore (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem gapClocks (negative : Bool) (stage : Fin 3) : FlatOperation.ConstraintsHoldFlat
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

theorem gapAccepted (negative : Bool) :
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

theorem gapImage (negative : Bool) :
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

theorem gapInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem gapRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (gapProgram negative) := by
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

theorem gapSeedScope (negative : Bool) : UnifiedReduced.Caller.ControlPreparation
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

theorem gapMiddleScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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

theorem gapLastScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation
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


def gapValue (negative : Bool) : BitVec 32 := (UnifiedReduced.Caller.ControlLiteral.addi (dataflowSeed negative)).value
theorem gapFramed (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
    (gapData negative) (gapProgram negative) 12 12 (gapValue negative) :=
  .frame (.prepared (.literal (gapSeedScope negative))) (gapMiddleScope negative) (by decide) (by decide)
theorem gapPreparation (negative : Bool) : UnifiedReduced.Caller.PublicRegisterDataflow
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

def forgedGapData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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
