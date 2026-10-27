import Slop.Sail.ResetState
import Slop.Trace.PooledHistory
import Slop.Trace.PooledCode
import Slop.Sail.WordMemoryState
import Slop.Sail.PhysicalMemory
import Tests.SubwordMemoryTimestamp

namespace Tests.PooledHistory
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- LBU x2,0(x1), then ADD x1,x2,x0. The corrupted ADD computes a consistent
-- local result from 19, but the preceding LBU wrote 18 to x2.
private def assignment (corrupt : Bool) : Nat → ZMod babyBearModulus
  | 0 | 35 => 4
  | 2 | 19 => 8
  | 21 => 12
  | 5 => 2
  | 23 => 6
  | 25 | 33 => if corrupt then 19 else 18
  | 31 | 4 | 7 | 10 | 42 | 43 | 44 => 1
  | 32 => 64
  | _ => 0

private def load : Row babyBearModulus PooledFamily :=
  ⟨.subwordMemory, Tests.SubwordMemoryTimestamp.assignment false⟩
private def add (corrupt : Bool) : Row babyBearModulus PooledFamily :=
  ⟨.addSub, assignment corrupt⟩
private def token (cell : Cell) (time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨cell.addressCode, (time, 0), Nat.pair lo hi⟩
private def trace (corrupt : Bool) : PooledTrace babyBearModulus where
  rows := [add corrupt, load]
  rom := ⟨ROM.table [] [], Verification.subwordTable (fun _ => 0)⟩
  initial := load.start
  terminal := (add corrupt).finish
  initialMemory := [token (.register 0) 0 0 0, token (.register 1) 0 1 64,
    token (.ram 4194304) 0 4660 22136, token (.register 2) 0 0 0]
  terminalMemory := [token (.register 0) 9 0 0, token (.register 1) 10 (if corrupt then 19 else 18) 0,
    token (.ram 4194304) 5 4660 22136, token (.register 2) 8 (if corrupt then 19 else 18) 0]

theorem local_add (corrupt : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment corrupt)) AddSub.clockConstraints := by
  cases corrupt <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, babyBearModulus])
    | norm_num [babyBearModulus]

theorem accepted : Accepted (trace false) := by
  constructor
  · intro row member
    simp [trace] at member
    rcases member with rfl | rfl
    · exact local_add false
    · exact Tests.SubwordMemoryTimestamp.constraints false
  · intro row member
    simp [trace] at member
    rcases member with rfl | rfl <;> rfl
  · have linked : load.finish = (add false).start := rfl
    change [load.start, (add false).finish, load.finish].Perm
      [(add false).finish, (add false).start, load.start]
    rw [linked]
    exact (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.swap _ _ []))
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, add, load, token,
      AddSub.importedConstraintsMemoryPorts, SubwordMemory.importedConstraintsMemoryPorts,
      AddSub.importedConstraintsTraceColumns, SubwordMemory.importedConstraintsTraceColumns]
    decide

private theorem boundary : ClockBoundary (trace false) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro token member
    simp [trace] at member
    rcases member with rfl | rfl | rfl | rfl <;> constructor <;> decide

/-- The two families receive their per-row clock obligations from one global
    native permutation, not from separately supplied row assumptions. -/
theorem derived_clocks : ∀ row ∈ (trace false).rows,
    ClockEffects row.columns row.assignment :=
  Proofs.trace_clocks (by decide) (by decide) accepted boundary

/-- The same generic latest-write proof spans the LBU-to-ADD dependency. -/
theorem latest_reads : ∀ row ∈ (trace false).rows, ∀ port ∈ row.ports,
    LatestRead (trace false) row port :=
  Proofs.latest_reads (by decide) (by decide) accepted boundary (by decide)

/-- Global matching rejects the fabricated cross-family read, although both
    rows separately satisfy their actual imported constraints and setups. -/
theorem fabricated_read_rejected : ¬ Accepted (trace true) := by
  intro accepted
  have matching := accepted.memory
  have present : token (.register 2) 6 18 0 ∈
      (trace true).initialMemory ++ (trace true).rows.flatMap Row.writes := by decide
  have absent : token (.register 2) 6 18 0 ∉
      (trace true).terminalMemory ++ (trace true).rows.flatMap Row.reads := by decide
  exact absent (matching.mem_iff.mp present)

private def cells : List Cell := [.register 0, .register 1, .ram 4194304, .register 2]
private def loadEntry : PooledProgramEntry :=
  ⟨0, 0x0000c103, .LOAD (0, .Regidx 1, .Regidx 2, true, 1),
    ⟨.subwordMemory, 1, 0, 2, ⟨0, 0⟩, 2, 0⟩⟩
private def addEntry : PooledProgramEntry :=
  ⟨4, 0x000100b3, .RTYPE (.Regidx 0, .Regidx 2, .Regidx 1, .ADD),
    ⟨.addSub, 2, 0, 1, ⟨0, 0⟩, 1, 0⟩⟩
private def initial : State :=
  { (default : State) with
    regs := ((default : State).regs).insert .x1 0x00400001
      |>.insert .x2 0 |>.insert .misa 0x40000100 |>.insert .PC 0 }
private def dataState := wordWriteState initial 4194304 0x56781234
private def codeState := wordWriteState dataState 0 loadEntry.bits
private noncomputable def before := wordWriteState codeState 4 addEntry.bits

theorem airbender_before  : Airbender.Reference.RiscV.Sail.Configured before := by
  configured_fixture [before, Airbender.Reference.RiscV.Sail.wordWriteState]


private theorem image : initialImage before cells = some (trace false).initialMemory := by
  have zero : (Cell.register 0).read before = .ok 0 before := rfl
  have one : (Cell.register 1).read before = .ok 0x00400001 before := by
    apply read_register
    simp [before, codeState, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok 0 before := by
    apply read_register
    simp [before, codeState, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 4194304).read before = .ok 0x56781234 before :=
    written_word_disjoint 4 addEntry.bits (Or.inr (by decide))
      (written_word_disjoint 0 loadEntry.bits (Or.inr (by decide))
        (written_word_read initial 4194304 0x56781234))
  simp only [initialImage, cells, List.mapM_cons, List.mapM_nil, zero, one, two, memory]
  rfl

private theorem program_image : pooledProgramImage before [0, 4] = some [loadEntry, addEntry] := by
  have loadBytes : (Cell.ram 0).read before = .ok loadEntry.bits before :=
    written_word_disjoint 4 addEntry.bits (Or.inl (by decide)) (written_word_read dataState 0 loadEntry.bits)
  have addBytes : (Cell.ram 4).read before = .ok addEntry.bits before := written_word_read _ 4 _
  have loadDecoded : Airbender.Reference.RiscV.Sail.decodeOnReset loadEntry.bits = some loadEntry.instruction :=
    by decode_on_reset
  have addDecoded : Airbender.Reference.RiscV.Sail.decodeOnReset addEntry.bits = some addEntry.instruction :=
    by decode_on_reset
  simp only [pooledProgramImage, List.mapM_cons, List.mapM_nil, programEntryWith,
    loadBytes, addBytes, loadDecoded, addDecoded, bind, Option.bind]
  rfl

private theorem decoded : PooledDecoded (trace false) [loadEntry, addEntry] := by
  intro row member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

/-- All mixed-family reads, writes and terminal values inherit canonical limbs
    from the actual public Sail image. No operand bound is provided to this proof. -/
theorem derived_values :
    (∀ row ∈ (trace false).rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ (trace false).rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ sink ∈ (trace false).terminalMemory, sink.word.Bounded) := by
  apply Proofs.pooled_value_bounds (by decide) (by decide) accepted boundary image
    (values := fun _ => 0) (programImage := program_image) (decoded := decoded)
  · rfl
  · rfl

/-- The same mixed trace transports its reads/writes through actual Sail GPR
    and byte-memory semantics. ISA-clause retirement is a later composition step. -/
theorem actual_cell_history :
    ∃ (history : TimestampSortedMemoryAccessList) (rows : List (Row babyBearModulus PooledFamily))
      (after : State),
      MemoryHistory (trace false) history ∧ rows.Perm (trace false).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents (trace false).memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  exact Proofs.pooled_native_history (by decide) (by decide) accepted boundary image
    (by decide) (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned])
    program_image decoded

/-- The full mixed history preserves both fetched public instructions. Their
    bytes and original Sail decoding remain linked after the native writes. -/
theorem preserved_program :
    ∃ (rows : List (Row babyBearModulus PooledFamily)) (after : State),
      rows.Perm (trace false).rows ∧
      SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents (trace false).memoryEpoch row).reverse) before after ∧
      loadEntry.SourceWith after pooledDecoderFields ∧ addEntry.SourceWith after pooledDecoderFields := by
  obtain ⟨_, rows, after, _, permutation, _, nativeHistory, _⟩ := actual_cell_history
  have eventPermutation :
      (rows.flatMap fun row => (Trace.rowEvents (trace false).memoryEpoch row).reverse).Perm
        (trace false).nativeEvents := by
    rw [Proofs.native_events_projection (by decide) (by decide) accepted boundary]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  refine ⟨rows, after, permutation, nativeHistory, ?_, ?_⟩
  all_goals
    exact Proofs.pooled_source_after_history (by decide) (by decide) accepted boundary image
      program_image (by simp) (by decide) (fun _ member => eventPermutation.mem_iff.mp member) nativeHistory

end Tests.PooledHistory
