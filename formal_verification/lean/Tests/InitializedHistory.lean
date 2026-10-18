import Tests.AddSub
import Airbender.Review.Trace.Initialization
import Airbender.Review.Trace.Decoder
import Airbender.Review.Trace.Values
import Airbender.Review.Trace.SailHistory
import Airbender.Review.Trace.PC
import Airbender.Proofs.Trace.Arithmetic
import Airbender.Review.Trace.Families.AddSub.Theorems
import Airbender.Proofs.Trace.PortReads
import Airbender.Proofs.Trace.AccessExecution

namespace Tests.InitializedHistory
open Airbender Trace
open Reference.Sail _root_.Sail.ArchSem

-- x1 + x1 -> x1. Readonly ports refresh the same cell at clocks 4 and 5;
-- the actual destination write at clock 6 replaces 123 with 246.
private def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 35 then 123 else if i = 47 then 4 else if i = 50 then 5
  else Tests.AddSub.row 1 123 123 0 246 0 0 0 0 0 4 0 0 0 i

private def nativeRow : Row mersenne31Modulus := ⟨.addSub, assignment⟩

private def cell (time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair 1 0), (time, 0), Nat.pair value 0⟩

private def trace : Data mersenne31Modulus where
  rows := [nativeRow]
  rom := ()
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(4, 0), (8, 0)⟩
  initialMemory := [cell 0 123]
  terminalMemory := [cell 6 246]

private theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    exact satisfies
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    decide
  · change [trace.initial, nativeRow.finish].Perm [trace.terminal, nativeRow.start]
    have start : nativeRow.start = trace.initial := rfl
    have finish : nativeRow.finish = trace.terminal := rfl
    rw [start, finish]
    exact List.Perm.swap _ _ []
  · change ([cell 0 123, cell 4 123, cell 5 123, cell 6 246]).Perm
      [cell 6 246, cell 0 123, cell 4 123, cell 5 123]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro token member
    have same : token = cell 0 123 := by simpa [trace] using member
    subst token
    constructor <;> decide

private theorem unique : (trace.initialMemory.map MemoryToken.address).Nodup := by decide

/-- Nonempty application of the public trace theorem with aliased ports. -/
theorem complete_history : ∃ history, MemoryHistory trace history :=
  (native_memory_soundness accepted boundary unique).1

/-- Destination's old value comes from the second readonly refresh, not the seed. -/
theorem destination_latest : LatestRead trace nativeRow
    Airbender.AddSub.importedConstraintsMemoryPorts[2] :=
  (native_memory_soundness accepted boundary unique).2 nativeRow (by simp [trace]) _ (by
    change Airbender.AddSub.importedConstraintsMemoryPorts[2] ∈
      Airbender.AddSub.importedConstraintsMemoryPorts
    simp [Airbender.AddSub.importedConstraintsMemoryPorts])

private def staleAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 47 then 0 else assignment i

private def staleRow : Row mersenne31Modulus := ⟨.addSub, staleAssignment⟩
private def staleTrace : Data mersenne31Modulus := { trace with rows := [staleRow] }

/-- Local native constraints alone allow reusing the seed for the second read. -/
theorem stale_local_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment staleAssignment)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, staleAssignment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

/-- Actual logical memory matching rejects that stale alias read. -/
theorem stale_history_rejected : ¬ Accepted staleTrace := by
  intro h
  have count := h.memory.count_eq (cell 4 123)
  revert count
  decide

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity)
    |>.insert .x1 (123 : BitVec 32) |>.insert .PC (0 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xb3 : BitVec 8)
    |>.insert 1 0x80 |>.insert 2 0x10 |>.insert 3 0
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private theorem public_inputs : ImageBoundary trace before [Cell.register 1] := by
  have read : (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (0 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage, List.mapM_cons, List.mapM_nil]
    rw [read]
    rfl
  · rw [initialState, pc]
    rfl

/-- The seed is now constructed from the original Sail read of public x1. -/
theorem public_image_history : ∃ history, MemoryHistory trace history :=
  (public_image_memory_soundness public_inputs accepted).1

-- Failure proofs follow the pinned source Tests/TraceInitialImage.lean.
/-- Missing public registers reject image construction rather than defaulting to zero. -/
theorem missing_register_rejected :
    initialImage (p := mersenne31Modulus) before [Cell.register 2] = none := by
  have absent : Cell.read (.register 2) before =
      .error _root_.Sail.Error.Unreachable before := by
    have missing : before.regs.get? .x2 = none := by
      simp [before, Std.ExtDHashMap.get?_insert]
    change run (SailRV32.readReg .x2) before = _
    dsimp [run, SailRV32.readReg, PreSail.readReg, interpretSailEffects, FreeM.liftM,
      interpretInstructionEffect]
    simp [missing, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.run]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

/-- Missing byte memory also rejects the public image constructor. -/
theorem missing_bytes_rejected :
    initialImage (p := mersenne31Modulus) before [Cell.ram 4] = none := by
  have absent : Cell.read (.ram 4) before =
      .error (_root_.Sail.Error.OutOfMemoryRange 4) before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, EStateM.bind, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw, before]
  simp only [initialImage, List.mapM_cons, absent]
  rfl

private def addEntry : ProgramEntry :=
  ⟨0, 0x001080b3, .RTYPE (.Regidx 1, .Regidx 1, .Regidx 1, .ADD),
    ⟨.addSub, 1, 1, 1, ⟨0, 0⟩, 1, 0⟩⟩

private def setup : DecoderSetup := ⟨[addEntry], 1⟩

set_option maxRecDepth 32768 in
/-- Actual public bytes and the pinned Sail decoder build the full padded setup. -/
theorem setup_built : decoderSetupImage before 1 1 = some setup := by
  have bytes : (Cell.ram 0).read before = .ok 0x001080b3 before := by
    simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
      bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert]
  have program : programImage before [0] = some [addEntry] := by
    simp only [List.mapM_cons, List.mapM_nil, programEntryWith,
      bytes, bind, Option.bind]
    rfl
  change (programImage before [0]).bind (fun entries => some ⟨entries, 1⟩) = some setup
  rw [program]
  rfl

private theorem decoded : Decoded trace setup := by
  intro row member
  have same : row = nativeRow := by simpa [trace] using member
  subst row
  change ∃ i : Fin 2, nativeRow.decoderQuery = setup.row i
  refine ⟨⟨0, by decide⟩, ?_⟩
  change nativeRow.decoderQuery = addEntry.query
  decide

theorem padding_retained : setup.row (p := mersenne31Modulus) ⟨1, by decide⟩ =
    Vector.replicate 10 (-1) := rfl

theorem native_padding_rejected : nativeRow.decoderQuery ≠ Vector.replicate 10 (-1) :=
  Trace.Proofs.padding_excluded (by decide) satisfies

theorem public_decode_source : ∃ entry ∈ setup.program,
    entry.Source before ∧ nativeRow.decoderQuery = entry.query :=
  public_decoder_soundness setup_built accepted decoded nativeRow (by simp [trace])

theorem decoder_word_bounds : nativeRow.start.word.Bounded ∧ nativeRow.decoderImmediate.Bounded :=
  Trace.Proofs.decoded_word_bounds (by decide) setup_built accepted decoded nativeRow (by simp [trace])

theorem initialized_read_bounds : ∀ port ∈ nativeRow.ports,
    (readToken assignment port).word.Bounded :=
  (public_image_value_bounds public_inputs accepted decoded).1 nativeRow (by simp [trace])

theorem initialized_terminal_bounds : ∀ token ∈ trace.terminalMemory, token.word.Bounded :=
  (public_image_value_bounds public_inputs accepted decoded).2.2

theorem setup_capacity_rejected : decoderSetupImage before 3 1 = none := rfl

-- An unconstrained decoder zero flag can make an otherwise valid masked write unbounded.
private def badAssignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 8 then 2 else if i = 37 then -246 else assignment i

private def badRow : Row mersenne31Modulus := ⟨.addSub, badAssignment⟩
private def badTrace : Data mersenne31Modulus := {trace with rows := [badRow]}

theorem bad_flag_local_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment badAssignment)
      Airbender.AddSub.importedConstraints := by
  simp [Airbender.AddSub.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    Verification.environment, badAssignment, assignment, Tests.AddSub.row]
  repeat' apply And.intro
  all_goals first | decide | (apply Verification.range16_contains; decide) |
    (apply Verification.timestamp19_contains; decide)

theorem bad_flag_write_unbounded :
    ¬ (writeToken badRow.columns badAssignment
      Airbender.AddSub.importedConstraintsMemoryPorts[2]).word.Bounded := by
  rw [Trace.Proofs.write_word]
  change ¬ ((-246 : ZMod mersenne31Modulus).val < 65536 ∧
    (0 : ZMod mersenne31Modulus).val < 65536)
  decide

/-- The full padded lookup rejects the bad flag instead of assuming bounds for it. -/
theorem bad_flag_decoder_rejected : ¬ Decoded badTrace setup := by
  intro decoded
  have member := decoded badRow (by simp [badTrace])
  obtain ⟨entry, present, equal⟩ := Trace.Proofs.decoder_member (by decide)
    bad_flag_local_satisfies member
  have same : entry = addEntry := by simpa [setup] using present
  subst entry
  have flag := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[5]) equal
  change (2 : ZMod mersenne31Modulus) = 0 at flag
  revert flag
  decide

private theorem aligned : ∀ cell ∈ [Cell.register 1], cell.Aligned := by
  intro cell member
  have same : cell = Cell.register 1 := by simpa using member
  subst cell
  trivial

/-- The public theorem derives actual Sail transfers for the accepted alias row. -/
theorem initialized_sail_history :
    ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess)
      (seed : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory trace history ∧ List.append (α := MemoryAccess) events seed.val = history.val ∧
      events.Perm trace.nativeEvents ∧ SailHistory [Cell.register 1] events before after ∧
      SailStateMatches [Cell.register 1] history after :=
  public_image_sail_history public_inputs accepted decoded aligned

private theorem native_row_history : ∃ after,
    SailHistory [Cell.register 1] (rowEvents trace.memoryEpoch nativeRow).reverse before after := by
  obtain ⟨_, rows, after, _, permutation, _, history, _⟩ :=
    Trace.Proofs.decoded_row_history (by decide) accepted boundary public_inputs.image
      public_inputs.domain aligned decoded
  have same : rows = [nativeRow] := List.perm_singleton.mp permutation
  subst rows
  exact ⟨after, by simpa using history⟩

/-- Readonly refreshes stutter even when all three addresses alias: the
    destination old-value read still comes from the original Sail pre-state. -/
theorem alias_destination_prestate_read :
    (Cell.register 1).read before = .ok (123 : BitVec 32) before := by
  obtain ⟨after, history⟩ := native_row_history
  have read := Trace.Proofs.row_history_read trace.memoryEpoch history
    (port := Airbender.AddSub.importedConstraintsMemoryPorts[2])
    (by change Airbender.AddSub.importedConstraintsMemoryPorts[2] ∈
          Airbender.AddSub.importedConstraintsMemoryPorts
        simp [Airbender.AddSub.importedConstraintsMemoryPorts])
    (cell := Cell.register 1) (by rfl)
  change (Cell.register 1).read before = .ok
    (memoryWord (Airbender.AddSub.importedConstraintsMemoryPorts[2].readCode assignment)) before at read
  have value : Airbender.AddSub.importedConstraintsMemoryPorts[2].readCode assignment =
      Nat.pair 123 0 := rfl
  rw [value, memoryWord, Nat.unpair_pair] at read
  exact read

/-- The grouped history supplies the actual Sail x1 write of 246. -/
theorem alias_actual_write : ∃ after,
    run (SailRV32.Functions.wX_bits (.Regidx 1) (246 : BitVec 32)) before = .ok () after := by
  obtain ⟨after, history⟩ := native_row_history
  have written := Trace.Proofs.addsub_history_register_write (by decide) trace.memoryEpoch history
    (entry := addEntry) (by decide)
  change run ((Cell.register 1).write
    (memoryWord (Airbender.AddSub.importedConstraintsMemoryPorts[2].writeCode assignment)))
      before = .ok () after at written
  have value : Airbender.AddSub.importedConstraintsMemoryPorts[2].writeCode assignment =
      Nat.pair 246 0 := rfl
  rw [value, memoryWord, Nat.unpair_pair] at written
  exact ⟨after, written⟩

/-- Actual public bytes/setup and native equations discharge all row PC inputs. -/
theorem initialized_pc_path : nativeRow.start.word.Bounded ∧ nativeRow.start.word.lo % 4 = 0 ∧
    nativeRow.finish.word.Bounded ∧ nativeRow.finish.word.toBitVec = nativeRow.start.word.toBitVec + 4 :=
  (public_pc_soundness public_inputs setup_built accepted decoded).1 nativeRow (by simp [trace])

theorem initialized_terminal_pc_bound : trace.terminal.word.Bounded :=
  (public_pc_soundness public_inputs setup_built accepted decoded).2

private def emptyTrace : Data mersenne31Modulus :=
  { trace with
    rows := []
    terminal := trace.initial
    terminalMemory := trace.initialMemory }

/-- With no participating rows, the external terminal PC is bounded from the
    actual public Sail initial PC, rather than an outgoing-row assumption. -/
theorem empty_terminal_pc_bound : emptyTrace.terminal.word.Bounded := by
  have inputs : ImageBoundary emptyTrace before [Cell.register 1] :=
    ⟨public_inputs.domain, public_inputs.image, public_inputs.initial⟩
  have accepted : Accepted emptyTrace := by
    constructor
    · intro row member; simp [emptyTrace] at member
    · intro row member; simp [emptyTrace] at member
    · exact List.Perm.refl _
    · exact List.Perm.refl _
  have setup : decoderSetupImage before 0 0 = some (DecoderSetup.mk [] 1) := rfl
  have decoded : Decoded emptyTrace ⟨[], 1⟩ := by
    intro row member; simp [emptyTrace] at member
  exact (public_pc_soundness inputs setup accepted decoded).2

/-- Native history and actual public decoding discharge every local interface
    and reach the original Sail ADD retirement state. -/
theorem initialized_sail_retirement : ∃ after,
    SailHistory [Cell.register 1] (rowEvents trace.memoryEpoch nativeRow).reverse before after ∧
    run (Reference.RiscV.Sail.normalStep
      (SailRV32.Functions.execute_RTYPE (.Regidx 1) (.Regidx 1) (.Regidx 1) .ADD)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after 4) := by
  obtain ⟨after, history⟩ := native_row_history
  refine ⟨after, history, ?_⟩
  have checked := Trace.Proofs.arithmetic_row_execution (w := assignment) (before := before)
    (by decide) public_inputs (Trace.Proofs.strict_indexed_program setup_built) accepted decoded
    (by simp [trace, nativeRow]) (entry := addEntry) rfl (by decide) .add 1 1 1 0 0 rfl history
    (Trace.Proofs.initial_state_pc (by decide) public_inputs.initial)
  exact checked

theorem initialized_sail_execution : Realizes (SailStep setup.program) trace before [Cell.register 1] :=
  public_sail_execution public_inputs setup_built accepted decoded aligned

/-- Empty native execution preserves the actual initialized cell image and PC. -/
theorem empty_sail_execution : Realizes (SailStep []) emptyTrace before [Cell.register 1] := by
  have inputs : ImageBoundary emptyTrace before [Cell.register 1] :=
    ⟨public_inputs.domain, public_inputs.image, public_inputs.initial⟩
  have accepted : Accepted emptyTrace := by
    constructor
    · intro row member; simp [emptyTrace] at member
    · intro row member; simp [emptyTrace] at member
    · exact List.Perm.refl _
    · exact List.Perm.refl _
  have image : decoderSetupImage before 0 0 = some (DecoderSetup.mk [] 1) := rfl
  have decoded : Decoded emptyTrace ⟨[], 1⟩ := by
    intro row member; simp [emptyTrace] at member
  exact public_sail_execution inputs image accepted decoded aligned

end Tests.InitializedHistory
