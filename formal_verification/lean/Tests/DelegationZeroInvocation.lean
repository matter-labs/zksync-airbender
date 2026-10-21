import Airbender.Review.Circuits.AddSub.CallerTheorems
import Airbender.Review.Trace.Delegation.CallerTheorems
import Airbender.Review.Trace.UnifiedReduced.Theorems
import Airbender.Review.Trace.Padding
import Airbender.Proofs.Blake2G.Claims
import Airbender.Proofs.Delegation.Requests
import Airbender.Proofs.Delegation.NativeInvocation
import Airbender.Proofs.Sail.WordMemoryState
import Mathlib.Tactic.IntervalCases
import Tests.DelegationCaller
import Airbender.Proofs.Trace.ImageFrame

namespace Tests.DelegationZeroInvocation
open Airbender Trace
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- The exact historical zero-invocation witness. The current timestamp
    constraint rejects it; its instruction/core arithmetic is unchanged. -/
private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 0 ∨ column = 5 ∨ column = 12 then 1
  else if column = 8 then 4
  else if column = 9 then 8
  else if column = 10 then 12
  else if column = 14 ∨ column = 31 ∨ column = 32 then 64
  else if 83 ≤ column ∧ column < 110 ∧ (column - 83) % 3 = 2 then 1
  else 0

private abbrev table : Table (ZMod babyBearModulus) (fields 9) :=
  Blake2G.setupTable Blake2G.Control.controllerRows

private def indices : Vector Nat 19 :=
  #v[344640, 0, 0, 0, 0, 65536, 82240, 65600, 65536, 82240, 65600,
    0, 0, 0, 0, 65856, 82240, 65856, 82240]

private theorem indexBound (i : Fin 19) : indices[i] < 344896 := by
  fin_cases i <;> decide

private theorem tableQuery (i : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints table)).get
      ⟨i.val + 2, by rw [Blake2G.lookup_count]; omega⟩).Contains (Verification.environment row) := by
  let index : Fin 344896 := ⟨indices[i], indexBound i⟩
  fin_cases i
  all_goals refine ⟨index, ?_⟩
  all_goals simp only [Blake2G.Proofs.setup_row_characterization]
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals change j < 9 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Blake2G.importedConstraints table) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.lookup_count] using hi
    by_cases small : i < 2
    · interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals decide
    · have source := tableQuery ⟨i - 2, by omega⟩
      have position : i - 2 + 2 = i := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

private def native : Delegation.Row babyBearModulus := ⟨.blakeG, row⟩
private def setup : Delegation.Setup babyBearModulus :=
  Delegation.modeledSetup (fun _ => Vector.replicate 6 0)
private def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd
private def cells : List Cell :=
  [.register 10, .ram 4194304, .ram 4194320, .ram 4194336, .ram 4194352,
    .register 11, .ram 4194368, .ram 4194372, .register 12]
private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x10 (4194304 : BitVec 32)
    |>.insert .x11 (4194368 : BitVec 32) |>.insert .x12 (0 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity)
    |>.insert 4194304 (0 : BitVec 8)
    |>.insert 4194305 (0 : BitVec 8)
    |>.insert 4194306 (0 : BitVec 8)
    |>.insert 4194307 (0 : BitVec 8)
    |>.insert 4194320 (0 : BitVec 8)
    |>.insert 4194321 (0 : BitVec 8)
    |>.insert 4194322 (0 : BitVec 8)
    |>.insert 4194323 (0 : BitVec 8)
    |>.insert 4194336 (0 : BitVec 8)
    |>.insert 4194337 (0 : BitVec 8)
    |>.insert 4194338 (0 : BitVec 8)
    |>.insert 4194339 (0 : BitVec 8)
    |>.insert 4194352 (0 : BitVec 8)
    |>.insert 4194353 (0 : BitVec 8)
    |>.insert 4194354 (0 : BitVec 8)
    |>.insert 4194355 (0 : BitVec 8)
    |>.insert 4194368 (0 : BitVec 8)
    |>.insert 4194369 (0 : BitVec 8)
    |>.insert 4194370 (0 : BitVec 8)
    |>.insert 4194371 (0 : BitVec 8)
    |>.insert 4194372 (0 : BitVec 8)
    |>.insert 4194373 (0 : BitVec 8)
    |>.insert 4194374 (0 : BitVec 8)
    |>.insert 4194375 (0 : BitVec 8)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private theorem initialized : initialImage before cells = some data.initial := by
  have x10 : Cell.read (.register 10) before = .ok 4194304 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) before = .ok 4194368 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, before, Std.ExtHashMap.getElem_insert,
    Cell.initialToken, data, native, Delegation.Row.memorySteps, Delegation.Row.ports,
    Blake2G.importedConstraintsMemoryPorts, readToken, MemoryAddress.code,
    Verification.IndirectPort.rawAddress, MemoryPort.readCode, WordColumns.code,
    WordColumns.evaluate, rawPair, row, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide

private def input : Blake2G.Input := ⟨⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
private def output : Blake2G.Words := ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩

theorem active_zero_invocation : row Blake2G.Variables.execute = 1 ∧
    (Delegation.Requests.fulfillment native).time = (0, 0) := by
  decide +kernel

theorem no_caller_virtual_matching :
    Delegation.Requests.Matching [] [Delegation.Requests.fulfillment native] := by
  exact Delegation.Requests.Proofs.zero_time_fulfillment_invisible _

private def sharedWorkers : Delegation.MemoryData babyBearModulus where
  setup := Delegation.modeledSetup Keccak.Controller.rows
  rows := [native]
  initial := data.initial
  terminal := data.terminal
private def sharedMachine : PooledTrace babyBearModulus where
  rows := []
  rom := ⟨{ name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩
  initial := ⟨(0, 0), (4, 0)⟩
  terminal := ⟨(0, 0), (4, 0)⟩
  initialMemory := data.initial
  terminalMemory := data.terminal
private def unifiedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := []
    rom := UnifiedReduced.Setup.table before
    initial := sharedMachine.initial
    terminal := sharedMachine.terminal
    initialMemory := data.initial
    terminalMemory := data.terminal }
  workers := sharedWorkers
  program := []

/-- The historical arithmetic witness still computes the zero G result. -/
theorem native_soundness : Blake2G.spec input output := by
  unfold Blake2G.spec
  decide +kernel

/-- Its native instruction/core constraints still hold. The new rejection is
    specifically supplied by the imported active-invocation timestamp query. -/
theorem historical_core_accepted : FlatOperation.ConstraintsHoldFlat
    (Verification.environment row) (Blake2G.importedConstraints table) := core

theorem active_zero_invocation_rejected : ¬ FlatOperation.ConstraintsHoldFlat
    (Verification.environment row) (native.constraints setup) := by
  intro accepted
  have live := Delegation.Proofs.active_invocation_live accepted
    (by decide +kernel : native.assignment native.columns.execute = 1)
  exact live active_zero_invocation.2

theorem unissued_worker_rejected : ¬ Delegation.MemoryAccepted data := by
  intro accepted
  exact active_zero_invocation_rejected
    (accepted.constraints native (List.mem_singleton_self _))

/-- Neither logical token cancellation nor padding filtering supplies the
    source fix: these two historical facts still hold for the raw witness. -/
theorem historical_memory_tokens_match :
    (data.initial ++ data.steps.map Prod.snd).Perm
      (data.terminal ++ data.steps.map Prod.fst) := List.perm_append_comm

theorem unissued_worker_survives_padding :
    native ∈ (UnifiedReduced.Caller.Padding.active unifiedData).workers.rows ∧
    (Delegation.Requests.fulfillment native).time = (0, 0) := by
  refine ⟨UnifiedReduced.Caller.Padding.Proofs.retained_worker
    (List.mem_singleton_self _) (by decide +kernel), active_zero_invocation.2⟩

open Arithmetic Reference.RiscV.Sail Reference.Sail

private theorem segmentationRegistry : UnifiedReduced.Caller.WrappedSequentialProgram [] := by
  constructor <;> intro _ member <;> cases member

private def issuedAssignment (column : Nat) : ZMod babyBearModulus := if column = 1 then 5 else row column
private def issuedWorker : Delegation.Row babyBearModulus := ⟨.blakeG, issuedAssignment⟩
private def issuedCallerAssignment (column : Nat) : ZMod babyBearModulus :=
  if column = 2 || column = 30 || column = 46 then 4
  else if column = 32 then 8
  else if column = 4 || column = 18 || column = 129 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else if column = 6 || column = 38 then Delegation.Requests.csr .blakeG else 0
private def issuedCaller : Trace.Row babyBearModulus UnifiedFamily := ⟨.machine, issuedCallerAssignment⟩
private def issuedBefore : Reference.RiscV.Sail.State :=
  wordWriteState before 0 (Tests.DelegationCaller.entry .blakeG).bits
private def issuedCells : List Cell := .register 0 :: cells
private def issuedData : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := [issuedCaller]
    rom := UnifiedReduced.Setup.table issuedBefore
    initial := issuedCaller.start
    terminal := issuedCaller.finish
    initialMemory := (Cell.register 0).initialToken 0 :: issuedWorker.memorySteps.map Prod.fst
    terminalMemory := UnifiedReduced.Caller.destinationToken issuedCallerAssignment :: issuedWorker.memorySteps.map Prod.snd }
  workers := { sharedWorkers with rows := [issuedWorker], initial := [], terminal := [] }
  program := [Tests.DelegationCaller.entry .blakeG]
private theorem issuedCore : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedAssignment)
    (Blake2G.importedConstraints table) := by
  simpa [Blake2G.importedConstraints, FlatOperation.ConstraintsHoldFlat, Verification.environment,
    Expression.eval, Lookup.Contains, timestampLookup, Table.toRaw, fromElements,
    issuedAssignment, row] using core
private theorem issuedClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedAssignment)
    Blake2G.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 21 := by simpa only [Blake2G.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel
private theorem issuedCallerCore : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedCallerAssignment)
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table issuedBefore)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, issuedCallerAssignment, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide +kernel)
    | (with_unfolding_all refine ⟨⟨0, by decide⟩, ?_⟩
       dsimp only
       rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
       simp only [UnifiedReduced.Setup.referenceRow, UnifiedReduced.Setup.referenceFixedRow,
         UnifiedReduced.Setup.referenceBinaryRow, Verification.shiftBinopRow_eq_reference]
       with_unfolding_all decide +kernel)
    | decide +kernel

private theorem issuedCallerClocks : FlatOperation.ConstraintsHoldFlat (Verification.environment issuedCallerAssignment)
    UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals decide +kernel
private theorem issuedAccepted : UnifiedReduced.Caller.MixedMemoryAccepted issuedData [] := by
  constructor
  · constructor
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact Verification.holds_append issuedCallerCore issuedCallerClocks
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      rfl
    · exact List.Perm.swap _ _ []
    · intro actual member
      have same : actual = issuedCaller := List.mem_singleton.mp member
      subst actual
      exact ⟨(0 : Fin 1), by decide +kernel⟩
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      exact Verification.holds_append issuedCore issuedClocks
    · intro actual member
      have same := List.mem_singleton.mp member
      subst actual
      rfl
    · have same : issuedData.calls = issuedData.fulfillments := by decide +kernel
      rw [← same]
      exact List.perm_append_comm
  · intro actual member ordinary
    have same := List.mem_singleton.mp member
    subst actual
    exact False.elim (ordinary (List.mem_singleton_self _))
  · decide +kernel
private theorem issuedInitialization : initialImage issuedBefore issuedCells = some issuedData.machine.initialMemory := by
  have seeds : initialImage before issuedCells = some issuedData.machine.initialMemory := by
    have same : issuedWorker.memorySteps.map Prod.fst = native.memorySteps.map Prod.fst := by decide +kernel
    change initialImage before (.register 0 :: cells) = some ((Cell.register 0).initialToken 0 :: issuedWorker.memorySteps.map Prod.fst)
    rw [same]
    have x0 : (Cell.register 0).read before = .ok 0 before := rfl
    have initial := initialized
    dsimp only [initialImage] at initial
    simp only [initialImage, List.mapM_cons, x0]
    rw [initial]
    rfl
  apply Trace.Proofs.image_frame seeds
  intro cell member value read
  cases cell with
  | register index => exact rX_register_frame (by dsimp only [issuedBefore, wordWriteState]) index read
  | ram address =>
    have lower : 4 ≤ address.toNat := by
      simp [issuedCells, cells] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals decide
    exact written_word_disjoint 0 _ (Or.inr lower) read
private theorem issuedInputs : UnifiedReduced.Caller.MixedMemoryInputs issuedData [] issuedBefore [0] [] issuedCells := by
  refine ⟨?_, rfl, issuedInitialization, by decide +kernel, ?_, rfl, rfl, ?_⟩
  · constructor
    · have bytes : (Cell.ram 0).read issuedBefore =
          .ok (Tests.DelegationCaller.entry .blakeG).bits issuedBefore := written_word_read _ 0 _
      have decoded : run
          (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry .blakeG).bits) issuedBefore =
          .ok (Tests.DelegationCaller.entry .blakeG).instruction issuedBefore := Tests.DelegationCaller.original_decoder .blakeG issuedBefore
      have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry .blakeG).instruction =
          some (Tests.DelegationCaller.entry .blakeG).data := Tests.DelegationCaller.metadata .blakeG
      simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage, programImageRunWith,
        List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields, bind, Option.bind, pure]
      rfl
    · change 4 < timestampBase ∧ 0 < timestampBase
      norm_num [timestampBase]
    · decide +kernel
  · intro cell member
    simp [issuedCells, cells] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Cell.Aligned]
  · intro actual member family
    have same := List.mem_singleton.mp member
    subst actual
    cases family
private def issuedWindow : UnifiedReduced.Caller.HashWindow := ⟨.blakeG true, 4, 8⟩
private theorem issuedCoverage : UnifiedReduced.Caller.ProgramHashCallerCoverage issuedData [issuedWindow] := by
  intro entry member _ clock lower upper aligned address
  have same := List.mem_singleton.mp member
  subst entry
  have selected : clock = 4 := by change 4 ≤ clock at lower; change clock + 4 ≤ 8 at upper; omega
  subst clock
  exact ⟨issuedWindow, List.mem_singleton_self _, by decide, by decide, rfl⟩

theorem issued_hash_worker_covered :
    ∃ window ∈ [issuedWindow], issuedWorker ∈ issuedData.workers.windowRows window.lower window.upper := by
  have covered := UnifiedReduced.Caller.Proofs.program_hash_worker_coverage (by decide +kernel) (by decide +kernel)
    issuedInputs.setup issuedAccepted issuedInputs.publicProgram issuedInputs.ordinaryProgram segmentationRegistry
    (windows := [issuedWindow]) (by intro window member; have same := List.mem_singleton.mp member; subst window; decide) issuedCoverage
  exact (covered issuedWorker (List.mem_singleton_self _) (by decide)).mpr (by decide +kernel)

theorem issued_hash_missing_window_rejected : ¬ UnifiedReduced.Caller.ProgramHashCallerCoverage issuedData [] := by
  intro coverage
  obtain ⟨window, member, _⟩ := coverage (Tests.DelegationCaller.entry .blakeG) (List.mem_singleton_self _)
    (by decide) 4 (by decide) (by decide) (by decide) rfl
  cases member

theorem issued_hash_partial_protocol_rejected :
    ¬ UnifiedReduced.Caller.WrappedProgramComputedProtocolWindowInputs issuedData [] issuedWindow := by
  intro scope
  have duration := scope.duration
  change 8 = 4 + 4 * 56 at duration
  contradiction

theorem issued_hash_worker_executes : UnifiedReduced.Caller.MixedMemoryEffects issuedData issuedBefore issuedCells :=
  UnifiedReduced.Caller.mixed_memory_soundness issuedAccepted issuedInputs

end Tests.DelegationZeroInvocation
