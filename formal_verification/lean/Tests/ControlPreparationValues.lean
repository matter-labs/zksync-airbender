import Tests.ControlPreparationBase

namespace Tests.ControlPreparation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def pcRelativePC (wrap : Bool) : BitVec 32 := if wrap then 0x10004 else 4
def pcRelativeImmediate (wrap : Bool) : BitVec 20 := if wrap then 0xfffff else 128
def pcRelativeBits (wrap : Bool) : BitVec 32 := if wrap then 0xfffff617 else 0x00080617
def pcRelativeValue (wrap : Bool) : BitVec 32 := if wrap then 61444 else 524292
def pcRelativeEntry (wrap : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨pcRelativePC wrap, pcRelativeBits wrap, .UTYPE (pcRelativeImmediate wrap, .Regidx 12, .AUIPC),
    ⟨.machine, 0, 0, 12, Word.ofBitVec (pcRelativeImmediate wrap ++ (0 : BitVec 12)), 4, 0⟩⟩
def pcRelativeBefore (wrap : Bool) : State := wordWriteState initialState (pcRelativePC wrap).toNat (pcRelativeBits wrap)
def pcRelativeCells : List Cell := [.register 0, .register 12]
def pcRelativeAssignment (wrap : Bool) (column : Nat) : ZMod babyBearModulus :=
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
def pcRelativeRow (wrap : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, pcRelativeAssignment wrap⟩
def pcRelativeData (wrap : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
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

theorem pcRelativeCore (wrap : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem pcRelativeClocks (wrap : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem pcRelativeAccepted (wrap : Bool) :
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

theorem pcRelativeProgram (wrap : Bool) :
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

theorem pcRelativeImage (wrap : Bool) :
    initialImage (pcRelativeBefore wrap) pcRelativeCells = some (pcRelativeData wrap).machine.initialMemory := by
  have zero : (Cell.register 0).read (pcRelativeBefore wrap) = .ok 0 (pcRelativeBefore wrap) := rfl
  have control : (Cell.register 12).read (pcRelativeBefore wrap) = .ok 65537 (pcRelativeBefore wrap) := by
    apply read_register
    simp [pcRelativeBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, pcRelativeCells, List.mapM_cons, List.mapM_nil, zero, control, bind, Option.bind]
  rfl

theorem pcRelativeInputs (wrap : Bool) :
    UnifiedReduced.Caller.MixedMemoryInputs (pcRelativeData wrap) [pcRelativeEntry wrap]
      (pcRelativeBefore wrap) [] [pcRelativePC wrap] pcRelativeCells := by
  refine ⟨⟨rfl, ?_, ?_⟩, pcRelativeProgram wrap, pcRelativeImage wrap, by decide, ?_, rfl, rfl, ?_⟩
  · cases wrap <;> change 4 < timestampBase ∧ 0 < timestampBase <;> norm_num [timestampBase]
  · cases wrap <;> decide +kernel
  · intro cell member
    simp [pcRelativeCells] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  · intro _ member; cases member

theorem pcRelativeScope (wrap : Bool) :
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

def forgedPCRelativeData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { pcRelativeData false with machine := { (pcRelativeData false).machine with
      rows := [⟨.machine, fun column => if column = 48 then 2 else pcRelativeAssignment false column⟩] } }

theorem auipc_fabricated_read_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedPCRelativeData [pcRelativeEntry false] := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 2 1⟩
  have member : token ∈ forgedPCRelativeData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedPCRelativeData.machine.initialMemory ++ forgedPCRelativeData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

def hashAUIPCMode (keccak : Bool) : Fin 3 := if keccak then 2 else 0
def hashAUIPCSpan (keccak : Bool) : Delegation.Caller.HashSpan := if keccak then .keccak else .blakeG true
def hashAUIPCPC (keccak : Bool) : BitVec 32 := if keccak then 4096 else 128
def hashAUIPCImmediate (keccak : Bool) : BitVec 20 := if keccak then 0xfffff else 0
def hashAUIPCBits (keccak : Bool) : BitVec 32 := if keccak then 0xfffff517 else 0x00000617
def hashAUIPCEntry (keccak : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨hashAUIPCPC keccak, hashAUIPCBits keccak,
    .UTYPE (hashAUIPCImmediate keccak, .Regidx (register (hashAUIPCMode keccak)), .AUIPC),
    ⟨.machine, 0, 0, register (hashAUIPCMode keccak), Word.ofBitVec (hashAUIPCImmediate keccak ++ (0 : BitVec 12)), 4, 0⟩⟩
def hashAUIPCBefore (keccak : Bool) : State := wordWriteState initialState (hashAUIPCPC keccak).toNat (hashAUIPCBits keccak)
def hashAUIPCAssignment (keccak : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 0 then (hashAUIPCPC keccak).toNat
  else if column = 30 then (hashAUIPCPC keccak).toNat + 4
  else if column = 11 then 0
  else if column = 13 then 1
  else if column = 8 then if keccak then 61440 else 0
  else if column = 9 then if keccak then 65535 else 0
  else if column = 52 || column = 53 then if keccak then 1 else 0
  else assignment (hashAUIPCMode keccak) column
def hashAUIPCRow (keccak : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, hashAUIPCAssignment keccak⟩
def hashAUIPCData (keccak : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data (hashAUIPCMode keccak) with machine := { (data (hashAUIPCMode keccak)).machine with
      rows := [hashAUIPCRow keccak]
      rom := UnifiedReduced.Setup.table (hashAUIPCBefore keccak)
      initial := (hashAUIPCRow keccak).start
      terminal := (hashAUIPCRow keccak).finish } }

theorem hashAUIPCCore (keccak : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem hashAUIPCClocks (keccak : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem hashAUIPCAccepted (keccak : Bool) :
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

theorem hashAUIPCProgram (keccak : Bool) :
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

theorem hashAUIPCImage (keccak : Bool) : initialImage (hashAUIPCBefore keccak) (cells (hashAUIPCMode keccak)) =
    some (hashAUIPCData keccak).machine.initialMemory := by
  have control : (Cell.register (register (hashAUIPCMode keccak))).read (hashAUIPCBefore keccak) =
      .ok 65537 (hashAUIPCBefore keccak) := by
    cases keccak <;> apply read_register
    all_goals simp [hashAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read (hashAUIPCBefore keccak) = .ok 0 (hashAUIPCBefore keccak) := rfl
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, control, bind, Option.bind]
  cases keccak <;> rfl

theorem hashAUIPCInputs (keccak : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (hashAUIPCData keccak)
    [hashAUIPCEntry keccak] (hashAUIPCBefore keccak) [] [hashAUIPCPC keccak] (cells (hashAUIPCMode keccak)) := by
  refine ⟨⟨rfl, ?_, ?_⟩, hashAUIPCProgram keccak, hashAUIPCImage keccak, ?_, ?_, rfl, rfl, ?_⟩
  · cases keccak <;> change 4 < timestampBase ∧ 0 < timestampBase <;> norm_num [timestampBase]
  · cases keccak <;> decide +kernel
  · cases keccak <;> decide +kernel
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> simp [Cell.Aligned]
  · intro _ member; cases member

theorem hashAUIPCScope (keccak : Bool) : UnifiedReduced.Caller.PCRelativePreparation (hashAUIPCData keccak)
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

theorem hashAUIPCPublicContext (keccak : Bool) :
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

def roundAUIPCEntry : UnifiedReduced.ProgramEntry :=
  ⟨524288, 0x00000617, .UTYPE (0, .Regidx 12, .AUIPC), ⟨.machine, 0, 0, 12, ⟨0, 0⟩, 4, 0⟩⟩
def roundAUIPCBefore : State := wordWriteState initialState 524288 0x00000617
def roundAUIPCAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 1 || column = 31 then 8
  else if column = 8 || column = 9 || column = 11 then 0
  else if column = 13 then 1
  else assignment 1 column
def roundAUIPCRow : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, roundAUIPCAssignment⟩
def roundAUIPCData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 1 with machine := { (data 1).machine with
      rows := [roundAUIPCRow]
      rom := UnifiedReduced.Setup.table roundAUIPCBefore
      initial := roundAUIPCRow.start
      terminal := roundAUIPCRow.finish } }

theorem roundAUIPCCore : FlatOperation.ConstraintsHoldFlat
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

theorem roundAUIPCClocks : FlatOperation.ConstraintsHoldFlat
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

theorem roundAUIPCAccepted : UnifiedReduced.Caller.MixedMemoryAccepted roundAUIPCData [roundAUIPCEntry] := by
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

theorem roundAUIPCProgram : UnifiedReduced.Mixed.programImage roundAUIPCBefore [524288] = some [roundAUIPCEntry] := by
  have bytes : (Cell.ram 524288).read roundAUIPCBefore = .ok 0x00000617 roundAUIPCBefore := written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00000617) roundAUIPCBefore =
      .ok roundAUIPCEntry.instruction roundAUIPCBefore := by with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields roundAUIPCEntry.instruction = some roundAUIPCEntry.data := by
    with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

theorem roundAUIPCImage : initialImage roundAUIPCBefore (cells 1) = some roundAUIPCData.machine.initialMemory := by
  have control : (Cell.register 12).read roundAUIPCBefore = .ok 65537 roundAUIPCBefore := by
    apply read_register
    simp [roundAUIPCBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read roundAUIPCBefore = .ok 0 roundAUIPCBefore := rfl
  simp only [initialImage, cells, register, show (1 : Fin 3).val = 1 from rfl, show ¬(1 : Nat) = 2 by decide,
    if_false, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  rfl

theorem roundAUIPCInputs : UnifiedReduced.Caller.MixedMemoryInputs roundAUIPCData [roundAUIPCEntry]
    roundAUIPCBefore [] [524288] (cells 1) := by
  refine ⟨⟨rfl, ?_, by decide +kernel⟩, roundAUIPCProgram, roundAUIPCImage,
    (inputs 1).distinct, (inputs 1).aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro _ member; cases member

theorem roundAUIPCScope : UnifiedReduced.Caller.PCRelativePreparation roundAUIPCData [roundAUIPCEntry] 8 12 0 := by
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

theorem roundAUIPCContext : UnifiedReduced.Caller.ProtocolContextInputs roundAUIPCData
    roundAUIPCBefore [] [524288] (cells 1) [roundAUIPCEntry] :=
  ⟨roundAUIPCInputs.publicProgram, roundAUIPCInputs.ordinaryProgram, roundAUIPCInputs.initialization,
    roundAUIPCInputs.distinct, roundAUIPCInputs.aligned, roundAUIPCInputs.setup, roundAUIPCInputs.tables⟩

theorem roundAUIPCRegion : UnifiedReduced.Caller.WrappedProgramComputedRoundRegionInputs
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

def registerImmediate (negative : Bool) : BitVec 12 := if negative then 0xfff else 128
def registerBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x08060613
def registerValue (negative : Bool) : BitVec 32 := if negative then 65536 else 65665
def registerEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, registerBits negative, .ITYPE (registerImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (registerImmediate negative)), 1, 0⟩⟩
def registerBefore (negative : Bool) : State := wordWriteState initialState 0 (registerBits negative)
def registerAssignment (negative : Bool) (column : Nat) : ZMod babyBearModulus :=
  if column = 5 then 12
  else if column = 36 || column = 37 || column = 51 then 1
  else if column = 46 then 4
  else if column = 40 then 0
  else if column = 8 then if negative then 65535 else 128
  else if column = 9 then if negative then 65535 else 0
  else if column = 50 then if negative then 0 else 129
  else if column = 52 || column = 53 then if negative then 1 else 0
  else assignment 0 column
def registerRow (negative : Bool) : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, registerAssignment negative⟩
def registerData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [registerRow negative]
      rom := UnifiedReduced.Setup.table (registerBefore negative)
      initial := (registerRow negative).start
      terminal := (registerRow negative).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
        ⟨(Cell.register 12).addressCode, (6, 0), Nat.pair (if negative then 0 else 129) 1⟩] } }

theorem registerCore (negative : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem registerClocks (negative : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem registerAccepted (negative : Bool) : UnifiedReduced.Caller.MixedMemoryAccepted (registerData negative) [registerEntry negative] := by
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

theorem registerProgram (negative : Bool) : UnifiedReduced.Mixed.programImage (registerBefore negative) [0] = some [registerEntry negative] := by
  have bytes : (Cell.ram 0).read (registerBefore negative) = .ok (registerBits negative) (registerBefore negative) := written_word_read _ _ _
  have decoded : Reference.Sail.run (SailRV32.Functions.encdec_backwards (registerBits negative)) (registerBefore negative) =
      .ok (registerEntry negative).instruction (registerBefore negative) := by cases negative <;> with_unfolding_all rfl
  have fields : UnifiedReduced.Mixed.decoderFields (registerEntry negative).instruction = some (registerEntry negative).data := by
    cases negative <;> with_unfolding_all rfl
  simp only [UnifiedReduced.Mixed.programImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
  rfl

theorem registerImage (negative : Bool) : initialImage (registerBefore negative) (cells 0) = some (registerData negative).machine.initialMemory := by
  have control : (Cell.register 12).read (registerBefore negative) = .ok 65537 (registerBefore negative) := by
    apply read_register
    simp [registerBefore, wordWriteState, initialState, Std.ExtDHashMap.get?_insert]
  have zero : (Cell.register 0).read (registerBefore negative) = .ok 0 (registerBefore negative) := rfl
  change initialImage (registerBefore negative) [.register 0, .register 12] = _
  simp only [initialImage, List.mapM_cons, List.mapM_nil, zero, control, bind, pure]
  rfl

theorem registerInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs (registerData negative)
    [registerEntry negative] (registerBefore negative) [] [0] (cells 0) := by
  refine ⟨⟨rfl, ?_, by cases negative <;> decide +kernel⟩, registerProgram negative, registerImage negative,
    (inputs 0).distinct, (inputs 0).aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · intro _ member; cases member

theorem registerScope (negative : Bool) : UnifiedReduced.Caller.RegisterImmediatePreparation (registerData negative)
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

def forgedRegisterData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { registerData false with machine := { (registerData false).machine with
      rows := [⟨.machine, fun column => if column = 36 then 2 else registerAssignment false column⟩] } }

theorem register_addi_fabricated_source_rejected :
    ¬ UnifiedReduced.Caller.MixedMemoryAccepted forgedRegisterData [registerEntry false] := by
  intro accepted
  let token : MemoryToken babyBearModulus := ⟨(Cell.register 12).addressCode, (0, 0), Nat.pair 2 1⟩
  have member : token ∈ forgedRegisterData.mixedSteps.map Prod.fst := by decide +kernel
  have absent : token ∉ forgedRegisterData.machine.initialMemory ++ forgedRegisterData.mixedSteps.map Prod.snd := by decide +kernel
  exact absent (accepted.memory.mem_iff.mpr (List.mem_append.mpr (Or.inr member)))

def dataflowSeed (negative : Bool) : BitVec 12 := if negative then 129 else 127
def dataflowImmediate (negative : Bool) : BitVec 12 := if negative then 0xfff else 1
def dataflowSeedBits (negative : Bool) : BitVec 32 := if negative then 0x08100613 else 0x07f00613
def dataflowBits (negative : Bool) : BitVec 32 := if negative then 0xfff60613 else 0x00160613
def dataflowBefore (negative : Bool) : State :=
  wordWriteState (wordWriteState initialState 0 (dataflowSeedBits negative)) 4 (dataflowBits negative)
def dataflowSeedEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨0, dataflowSeedBits negative, (.addi (dataflowSeed negative) : UnifiedReduced.Caller.ControlLiteral).instruction 12,
    ⟨.machine, 0, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowSeed negative)), 1, 0⟩⟩
def dataflowEntry (negative : Bool) : UnifiedReduced.ProgramEntry :=
  ⟨4, dataflowBits negative, .ITYPE (dataflowImmediate negative, .Regidx 12, .Regidx 12, .ADDI),
    ⟨.machine, 12, 0, 12, Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) (dataflowImmediate negative)), 1, 0⟩⟩
def dataflowProgram (negative : Bool) : List UnifiedReduced.ProgramEntry :=
  [dataflowSeedEntry negative, dataflowEntry negative]
def dataflowAssignment (negative second : Bool) (column : Nat) : ZMod babyBearModulus :=
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
def dataflowRow (negative second : Bool) : Trace.Row babyBearModulus UnifiedFamily :=
  ⟨.machine, dataflowAssignment negative second⟩
def dataflowData (negative : Bool) : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
  { data 0 with machine := { (data 0).machine with
      rows := [dataflowRow negative true, dataflowRow negative false]
      rom := UnifiedReduced.Setup.table (dataflowBefore negative)
      terminal := (dataflowRow negative true).finish
      terminalMemory := [⟨(Cell.register 0).addressCode, (9, 0), 0⟩,
        ⟨(Cell.register 12).addressCode, (10, 0), Nat.pair 128 0⟩] } }

theorem dataflowCore (negative second : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem dataflowClocks (negative second : Bool) : FlatOperation.ConstraintsHoldFlat
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

theorem dataflowAccepted (negative : Bool) :
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

theorem dataflowImage (negative : Bool) :
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

theorem dataflowInputs (negative : Bool) : UnifiedReduced.Caller.MixedMemoryInputs
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

theorem dataflowRegistry (negative : Bool) : UnifiedReduced.Caller.WrappedSequentialProgram (dataflowProgram negative) := by
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

theorem dataflowScope (negative : Bool) : UnifiedReduced.Caller.LiteralAddiPreparation
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

def forgedDataflowData : UnifiedReduced.Caller.RequestTrace babyBearModulus :=
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


end Tests.ControlPreparation
