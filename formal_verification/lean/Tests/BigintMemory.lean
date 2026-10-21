import Airbender.Proofs.Bigint.Claims

namespace Tests.BigintMemory
open Airbender Trace Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def row (column : Nat) : ZMod babyBearModulus :=
  if column = 1 then 5
  else if column = 4 || column = 38 then 64
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if 217 ≤ column ∧ column < 274 ∧ (column - 217) % 3 = 2 then 1
  else 0

private def native : Delegation.Row babyBearModulus := ⟨.bigint, row⟩

private def referenceRow (index : Fin 1390592) : Nat × Nat × Nat :=
  if index.val < 262144 then (index.val / 512, index.val % 512, 22)
  else if index.val < 1310720 then ((index.val - 262144) / 1024, (index.val - 262144) % 1024, 23)
  else if index.val < 1312768 then (index.val - 1310720, 0, 24)
  else if index.val < 1316864 then (index.val - 1312768, 0, 25)
  else if index.val < 1325056 then (index.val - 1316864, 0, 26)
  else (index.val - 1325056, (index.val - 1325056) % 256, 41)

private theorem lookup_relation (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (env : Environment (ZMod babyBearModulus)) :
    (Lookup.mk Bigint.setupTable.toRaw entry).Contains env ↔
      ∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((referenceRow i).1 : ZMod babyBearModulus),
          ((referenceRow i).2.1 : ZMod babyBearModulus),
          ((referenceRow i).2.2 : ZMod babyBearModulus)] := by
  change (∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((Bigint.setupRow i).1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.2 : ZMod babyBearModulus)]) ↔ _
  simp only [Bigint.Proofs.setup_row_characterization, referenceRow]

theorem core : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraints Bigint.setupTable) := by
  simp [Bigint.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, row, lookup_relation]
  repeat' apply And.intro
  all_goals solve
    | (apply Verification.range16_contains; decide)
    | (apply Trace.Proofs.range_contains; decide)
    | (refine ⟨⟨0, by decide⟩, ?_⟩; simp only [referenceRow]; decide)
    | (refine ⟨⟨262144, by decide⟩, ?_⟩; simp only [referenceRow]; decide)
    | (refine ⟨⟨1310720, by decide⟩, ?_⟩; simp only [referenceRow]; decide)
    | (refine ⟨⟨1312768, by decide⟩, ?_⟩; simp only [referenceRow]; decide)
    | (refine ⟨⟨1316864, by decide⟩, ?_⟩; simp only [referenceRow]; decide)
    | (refine ⟨⟨1325056, by decide⟩, ?_⟩; simp only [referenceRow]; decide)

private theorem clocks : FlatOperation.ConstraintsHoldFlat (Verification.environment row)
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, row]
  all_goals decide

private def setup : Delegation.Setup babyBearModulus :=
  ⟨Bigint.setupTable, { name := "unused", Contains _ _ := False },
    { name := "unused", Contains _ _ := False }, { name := "unused", Contains _ _ := False }⟩

def cells : List Cell :=
  [.register 10] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194304 + 4 * i))) ++
    [.register 11] ++ (List.range 8).map (fun i => .ram (BitVec.ofNat 32 (4194336 + 4 * i))) ++
    [.register 12]

def before : Reference.RiscV.Sail.State where
  regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x10 (4194304 : BitVec 32)
    |>.insert .x11 (4194336 : BitVec 32) |>.insert .x12 (128 : BitVec 32)
  mem := (List.range 64).foldl (fun memory i => memory.insert (4194304 + i) (0 : BitVec 8))
    (Std.ExtHashMap.emptyWithCapacity)
  tags := ()
  cycleCount := 0
  sailOutput := #[]

def data : Delegation.MemoryData babyBearModulus where
  setup := setup
  rows := [native]
  initial := native.memorySteps.map Prod.fst
  terminal := native.memorySteps.map Prod.snd

theorem accepted : Delegation.MemoryAccepted data := by
  constructor
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    exact Verification.holds_append core clocks
  · exact List.perm_append_comm

theorem initialized : initialImage before cells = some data.initial := by
  have x10 : Cell.read (.register 10) before = .ok 4194304 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x11 : Cell.read (.register 11) before = .ok 4194336 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have x12 : Cell.read (.register 12) before = .ok 128 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  norm_num [cells, List.range_succ, initialImage, List.mapM_cons, List.mapM_nil, x10, x11, x12]
  simp [Cell.read, _root_.Sail.ArchSem.readBytes,
    _root_.Sail.ArchSem.readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before, List.range_succ,
    Std.ExtHashMap.getElem_insert, Cell.initialToken, data, native, Delegation.Row.memorySteps,
    Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts,
    readToken, MemoryAddress.code, Verification.IndirectPort.rawAddress, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, rawPair, row, Word.ofBitVec, limbBase]
  all_goals decide

theorem inputs : Bigint.Memory.Inputs data before cells := by
  constructor
  · constructor
    · exact initialized
    · decide +kernel
    · intro current member
      simp only [data, List.mem_singleton] at member
      subst current
      decide
    · intro current member
      simp only [data, List.mem_singleton] at member
      subst current
      decide
  · intro current member
    simp only [data, List.mem_singleton] at member
    subst current
    rfl
  · rfl

theorem initialized_addresses :
    Bigint.Addresses.spec ⟨⟨0, 64⟩, ⟨32, 64⟩⟩
      (Bigint.importedConstraintsIndirectPorts.map (fun port => port.address row)) := by
  apply Bigint.Memory.addresses_soundness (by decide) (by decide) data before cells
    _ _ row
  refine ⟨inputs, accepted, ?_⟩
  constructor
  · constructor <;> rfl
  · simp [data, native]

theorem initialized_bounds :
    (∀ current ∈ data.rows, ∀ port ∈ current.ports, (readToken current.assignment port).word.Bounded) ∧
    (∀ current ∈ data.rows, ∀ port ∈ current.ports, (current.writeToken port).word.Bounded) ∧
    (∀ token ∈ data.terminal, token.word.Bounded) :=
  Bigint.Memory.native_value_bounds (by decide) accepted inputs

theorem native_operation_execution : Delegation.MemoryExecution data before cells ∧
    Bigint.Native.ArithmeticEffects row := by
  have aligned : ∀ cell ∈ cells, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | ⟨i, bound, rfl⟩ | rfl | ⟨i, bound, rfl⟩ | rfl
    all_goals first | trivial | (unfold Cell.Aligned; interval_cases i <;> decide)
  have result := Bigint.Native.operation_execution accepted inputs.publicState aligned rfl
  exact ⟨result.1, result.2 native (by simp [data]) rfl⟩

end Tests.BigintMemory
