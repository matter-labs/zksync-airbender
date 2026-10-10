import Tests.KeccakTheta
import Airbender.Review.Delegation.Theorems

namespace Tests.DelegationMemory
open Airbender Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 4
  else if column = 14 then 64
  else if 222 ≤ column ∧ column < 264 ∧ (column - 222) % 3 = 2 then 1
  else Tests.KeccakTheta.row column

private def native : Delegation.Row babyBearModulus := ⟨.keccak, row⟩

private theorem queries_unchanged (i : Fin 42) :
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment row)) =
    ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup)).get
      ⟨i.val, by rw [Keccak.lookup_count]; exact i.isLt⟩).entry.map
      (Expression.eval (Verification.environment Tests.KeccakTheta.row)) := by
  fin_cases i
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals first | change j < 1 at hj | change j < 8 at hj
  all_goals interval_cases j
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraints Tests.KeccakTheta.setup) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · decide
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have old := Verification.lookup_of_holds Tests.KeccakTheta.satisfies ⟨i, hi⟩
    have bound : i < 42 := by simpa only [Keccak.lookup_count] using hi
    have same := queries_unchanged ⟨i, bound⟩
    simp only [List.get_eq_getElem] at same old
    simp only [Lookup.Contains, Verification.environment] at old ⊢
    exact Eq.mp (congrArg (fun entry =>
      ((FlatOperation.lookups (Keccak.importedConstraints Tests.KeccakTheta.setup))[i]).table.Contains
        #[] entry) same.symm) old

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Keccak.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Keccak.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i hi
    have bound : i < 30 := by simpa only [Keccak.timestamp_count] using hi
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals norm_num [Keccak.importedConstraintsTimestampLookups, FlatOperation.lookups,
      Expression.eval, Verification.environment, row, Tests.KeccakTheta.row,
      Trace.timestampBase, ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus]

private def setup : Delegation.Setup babyBearModulus :=
  ⟨{ name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, Tests.KeccakTheta.setup⟩

private def cells : List Cell :=
  [.register 10, .register 11, .ram 4194304, .ram 4194308, .ram 4194344, .ram 4194348, .ram 4194384, .ram 4194388,
    .ram 4194424, .ram 4194428, .ram 4194464, .ram 4194468, .ram 4194504, .ram 4194508]

private def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x10 (3 : BitVec 32)
    |>.insert .x11 (4194304 : BitVec 32)
  mem := (Std.ExtHashMap.emptyWithCapacity)
    |>.insert 4194304 (255 : BitVec 8)
    |>.insert 4194305 (255 : BitVec 8)
    |>.insert 4194306 (255 : BitVec 8)
    |>.insert 4194307 (255 : BitVec 8)
    |>.insert 4194308 (255 : BitVec 8)
    |>.insert 4194309 (255 : BitVec 8)
    |>.insert 4194310 (255 : BitVec 8)
    |>.insert 4194311 (255 : BitVec 8)
    |>.insert 4194344 (255 : BitVec 8)
    |>.insert 4194345 (255 : BitVec 8)
    |>.insert 4194346 (255 : BitVec 8)
    |>.insert 4194347 (255 : BitVec 8)
    |>.insert 4194348 (255 : BitVec 8)
    |>.insert 4194349 (255 : BitVec 8)
    |>.insert 4194350 (255 : BitVec 8)
    |>.insert 4194351 (255 : BitVec 8)
    |>.insert 4194384 (255 : BitVec 8)
    |>.insert 4194385 (255 : BitVec 8)
    |>.insert 4194386 (255 : BitVec 8)
    |>.insert 4194387 (255 : BitVec 8)
    |>.insert 4194388 (255 : BitVec 8)
    |>.insert 4194389 (255 : BitVec 8)
    |>.insert 4194390 (255 : BitVec 8)
    |>.insert 4194391 (255 : BitVec 8)
    |>.insert 4194424 (255 : BitVec 8)
    |>.insert 4194425 (255 : BitVec 8)
    |>.insert 4194426 (255 : BitVec 8)
    |>.insert 4194427 (255 : BitVec 8)
    |>.insert 4194428 (255 : BitVec 8)
    |>.insert 4194429 (255 : BitVec 8)
    |>.insert 4194430 (255 : BitVec 8)
    |>.insert 4194431 (255 : BitVec 8)
    |>.insert 4194464 (255 : BitVec 8)
    |>.insert 4194465 (255 : BitVec 8)
    |>.insert 4194466 (255 : BitVec 8)
    |>.insert 4194467 (255 : BitVec 8)
    |>.insert 4194468 (255 : BitVec 8)
    |>.insert 4194469 (255 : BitVec 8)
    |>.insert 4194470 (255 : BitVec 8)
    |>.insert 4194471 (255 : BitVec 8)
    |>.insert 4194504 (1 : BitVec 8)
    |>.insert 4194505 (0 : BitVec 8)
    |>.insert 4194506 (0 : BitVec 8)
    |>.insert 4194507 (0 : BitVec 8)
    |>.insert 4194508 (0 : BitVec 8)
    |>.insert 4194509 (0 : BitVec 8)
    |>.insert 4194510 (0 : BitVec 8)
    |>.insert 4194511 (1 : BitVec 8)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

private def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

private theorem initialized : initialImage before cells = some data.initial := by
  have x10 : Cell.read (.register 10) before = .ok 3 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) before = .ok 4194304 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, x10, x11]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes,
    _root_.Sail.ArchSem.readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, data, native, Delegation.Row.memorySteps,
    Delegation.Row.ports, Keccak.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Tests.KeccakTheta.row,
    Arithmetic.Word.ofBitVec, Arithmetic.limbBase]
  all_goals decide

private theorem inputs : Delegation.MemoryInputs data before cells := by
  constructor
  · exact initialized
  · decide
  · intro actual member
    simp only [data, List.mem_singleton] at member
    subst actual
    decide

theorem native_memory_soundness : Delegation.MemorySoundness data :=
  Delegation.memory_soundness (by decide) accepted inputs

end Tests.DelegationMemory
