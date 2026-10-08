import Airbender.Review.Trace.Theorems

namespace Tests.TraceMemory
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- ADD x2,x1,x0 with x1 initially five. Clean's zero-initial memory must receive
-- an explicit initialization write before this nonzero operand can be read.
private def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 19 then 4
  else if v = 21 then 8
  else if v = 4 ∨ v = 5 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 7 then 2
  else if v = 25 ∨ v = 33 then 5
  else 0

private def row : Trace.Row babyBearModulus := ⟨.addSub, assignment⟩

private def token (register clock value : Nat) : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (clock, 0), Nat.pair value 0⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := [token 0 0 0, token 1 0 5, token 2 0 0]
  terminalMemory := [token 0 5 0, token 1 4 5, token 2 6 5]

theorem local_satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact local_satisfies
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp only [trace]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.ClockBoundary (trace rom) := by
  dsimp only [trace]
  constructor
  · change 4 < Trace.timestampBase ∧ 0 < Trace.timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem nonzero_clean_histories (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∀ source ∈ (trace rom).initialMemory, ∃ history, Trace.CellHistory (trace rom) source history := by
  apply Trace.cell_histories (accepted rom) (boundary rom)
  change ([token 0 0 0, token 1 0 5, token 2 0 0].map Trace.MemoryToken.address).Nodup
  decide

theorem merged_clean_history (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ history, Trace.MemoryHistory (trace rom) history := by
  apply Trace.memory_history (accepted rom) (boundary rom)
  change ([token 0 0 0, token 1 0 5, token 2 0 0].map Trace.MemoryToken.address).Nodup
  decide

-- The second instruction reads the value written by the first, twice, then
-- writes ten to x1. Rows are stored in reverse execution order.
private def secondAssignment (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 35 then 4
  else if v = 2 ∨ v = 19 ∨ v = 27 then 8
  else if v = 21 then 12
  else if v = 4 ∨ v = 7 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 5 ∨ v = 6 then 2
  else if v = 23 then 6
  else if v = 25 ∨ v = 29 ∨ v = 31 then 5
  else if v = 33 then 10
  else if v = 41 then 25 * 943718400 -- Shared Montgomery product intermediate.
  else 0

private def secondRow : Trace.Row babyBearModulus := ⟨.addSub, secondAssignment⟩
private def twoRows (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Data babyBearModulus :=
  { trace rom with
    rows := [secondRow, row]
    terminal := secondRow.finish
    terminalMemory := [token 0 5 0, token 1 10 10, token 2 9 5] }

theorem second_satisfies : FlatOperation.ConstraintsHoldFlat
    (Verification.environment secondAssignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, secondAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, secondAssignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, secondAssignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

theorem two_accepted (rom : Table (ZMod babyBearModulus) (fields 9)) : Trace.Accepted (twoRows rom) := by
  constructor
  · intro actual member
    simp only [twoRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact second_satisfies
    · exact local_satisfies
  · intro actual member
    simp only [twoRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · dsimp only [twoRows, trace]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · dsimp only [twoRows, trace]
    decide

theorem reordered_memory_history (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ history, Trace.MemoryHistory (twoRows rom) history := by
  apply Trace.memory_history (two_accepted rom)
  · exact ⟨(boundary rom).initial, (boundary rom).aligned, (boundary rom).memory⟩
  · change ([token 0 0 0, token 1 0 5, token 2 0 0].map Trace.MemoryToken.address).Nodup
    decide

private def zeroTable : Table (ZMod babyBearModulus) (fields 9) := .fromStatic {
  name := "TraceValueFixture"
  length := 1
  row _ := Vector.replicate 9 0
  index _ := 0
  Spec entry := entry = Vector.replicate 9 0
  contains_iff _ := by simp
}

private theorem value_boundary : Trace.ValueBoundary (trace zeroTable) := by
  constructor
  · intro actual member
    simp [trace] at member
    rcases member with rfl | rfl | rfl <;>
      norm_num [Trace.MemoryToken.word, token, Arithmetic.Word.Bounded, Arithmetic.limbBase]
  · intro entry member _
    obtain ⟨i, rfl⟩ := member
    exact ⟨rfl, rfl⟩
  · intro entry member
    obtain ⟨i, rfl⟩ := member
    simp [Arithmetic.limbBase]

-- The nonzero public x1 value and its arithmetic result reach every actual
-- read and terminal cell. No read-value or per-read range premise is supplied.
theorem bounded_native_values :
    (∀ actual ∈ (trace zeroTable).rows, ∀ port ∈ actual.ports,
      (Trace.readToken actual.assignment port).word.Bounded) ∧
    (∀ cell ∈ (trace zeroTable).terminalMemory, cell.word.Bounded) :=
  ⟨Trace.read_bounds (accepted zeroTable) (boundary zeroTable) value_boundary,
    Trace.terminal_bounds (accepted zeroTable) (boundary zeroTable) value_boundary⟩

private def before : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .PC (0 : BitVec 32) }

theorem native_pc_bounds :
    (∀ actual ∈ (trace zeroTable).rows, actual.start.word.Bounded ∧ actual.finish.word.Bounded) ∧
      (trace zeroTable).terminal.word.Bounded := by
  apply Trace.pc_bounds (accepted zeroTable) (before := before) (timestamp := (4, 0))
  have pcRead : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  rw [Trace.initialState, pcRead]
  rfl

private def publicBefore : Reference.RiscV.Sail.State :=
  { before with
    regs := before.regs.insert .x1 (5 : BitVec 32) |>.insert .x2 0
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0x33 : BitVec 8)
      |>.insert 1 0x81 |>.insert 2 0 |>.insert 3 0 }

private def publicProgram : List Trace.ProgramEntry :=
  [⟨0, 0x00008133, .RTYPE (.Regidx 0, .Regidx 1, .Regidx 2, .ADD),
    ⟨.addSub, 1, 0, 2, ⟨0, 0⟩, 1⟩⟩]

theorem public_program_image : Trace.programImage publicBefore [0] = some publicProgram := by
  have bytes : (Trace.Cell.ram 0).read publicBefore = .ok 0x00008133 publicBefore := by
    simp [Trace.Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      publicBefore, Std.ExtHashMap.getElem_insert]
  have instruction : Reference.Sail.run (SailRV32.Functions.encdec_backwards 0x00008133)
      publicBefore = .ok (.RTYPE (.Regidx 0, .Regidx 1, .Regidx 2, .ADD)) publicBefore := by rfl
  simp only [Trace.programImage, List.mapM_cons, List.mapM_nil, Trace.programEntry,
    bytes, bind, Option.bind, instruction]
  rfl

-- The complete accepted native row, not an isolated query, obtains its actual
-- fetched instruction and all nine selector bits from the public byte image.
theorem native_decoder_binding :
    ∀ actual ∈ (trace zeroTable).rows, actual.Fetched publicBefore := by
  apply Trace.decoder_soundness (accepted zeroTable) public_program_image
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, row.decoderQuery = _
  exact ⟨0, by decide⟩

theorem public_initial_image : Trace.initialImage publicBefore
    [.register 0, .register 1, .register 2] = some (trace zeroTable).initialMemory := by
  have zero : (Trace.Cell.register 0).read publicBefore = .ok 0 publicBefore := rfl
  have one : (Trace.Cell.register 1).read publicBefore = .ok 5 publicBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [publicBefore, Std.ExtDHashMap.get?_insert]
  have two : (Trace.Cell.register 2).read publicBefore = .ok 0 publicBefore := by
    apply Reference.RiscV.Sail.read_register
    simp [publicBefore]
  simp only [Trace.initialImage, List.mapM_cons, List.mapM_nil, zero, one, two,
    bind, Option.bind]
  rfl

theorem bounded_native_addresses :
    ∀ actual ∈ (trace zeroTable).rows, ∀ port ∈ actual.ports,
      (port.address.word actual.assignment).Bounded :=
  Trace.address_bounds (accepted zeroTable) (boundary zeroTable) public_initial_image

-- Equal combined address values are insufficient: the native pair encoding
-- rejects (65536, 0) as a representation of the canonical address (0, 1).
theorem noncanonical_ram_rejected :
    (Trace.MemoryAddress.mixed 10 false #v[25, 26]).code
      (fun v => if v = 10 then 1 else if v = 25 then (65536 : ZMod babyBearModulus) else 0) ≠
    (Trace.Cell.ram 65536).addressCode := by decide

end Tests.TraceMemory
