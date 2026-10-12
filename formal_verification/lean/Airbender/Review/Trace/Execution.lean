import Airbender.Review.Trace.Program
import Airbender.Review.Trace.ROM
import Airbender.Review.Trace.Platform
import Airbender.Review.Trace.Values
import Mathlib.Logic.Relation

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Dispatch original Sail memory clauses or the shared register/control dispatcher.
    Unsupported instruction constructors have no execution clause. -/
def instructionClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .LOAD (imm, rs1, rd, unsigned, size) =>
    some (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned size)
  | .STORE (imm, rs2, rs1, size) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 size)
  | instruction => registerClause instruction

/-- Select unchanged Sail semantics or the explicitly documented LW-to-x0
    Airbender deviation. The selected profile is visible in the execution claim. -/
inductive ISAProfile where
  | sail
  | airbender

/-- The pinned Airbender ISA table makes LW-to-x0 a PC-only NOP, even for
    unaligned addresses (`vendor/airbender/00-master.md`, LW row). Implement
    that one deviation with the original Sail ADDI x0,x0,0 clause. All other
    selected instructions execute their unchanged original Sail clauses. -/
def profileClause (profile : ISAProfile) (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  match profile, instruction with
  | .airbender, .LOAD (_, _, .Regidx 0, false, 4) =>
    some (SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI)
  | _, _ => instructionClause instruction

/-- One successful instruction from Sail state `before` to `after`. `program`
    holds entries built from public bytes; `projection` selects native decoder
    metadata and `clauseFor` selects the original Sail execution clause or a
    named profile deviation.

    Fetch/decoding must succeed in `before`, its PC must match the entry, and
    Sail preparation, execution and retirement must reach `after`. This is the
    reference relation proved by soundness, not an assumed circuit result. -/
def StepWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult))
    (program : List (ProgramEntry Kind)) (before after : State) : Prop :=
  ∃ entry ∈ program, entry.SourceWith before projection ∧
    run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before ∧
    ∃ clause, clauseFor entry.instruction = some clause ∧
      run (normalStep clause) before = .ok SailRV32.Functions.RETIRE_SUCCESS after

abbrev Step (profile : ISAProfile) := StepWith decoderFields (profileClause profile)

/-- A finite sequence of the checked Sail steps, including an empty trace. -/
abbrev ExecutionTrace (profile : ISAProfile) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step profile program)

abbrev SailStep := Step .sail
abbrev SailTrace := ExecutionTrace .sail
abbrev AirbenderTrace := ExecutionTrace .airbender

/-- The shared conclusion of trace soundness. Starting at public Sail state
    `initial`, a finite sequence of `step` reaches an `after` state whose PC
    and tracked register/RAM values match `trace`'s terminal tokens.

    `cells` is the public tracked address domain. `view` normally leaves tokens
    unchanged; native boot uses `ROMView.token initial` to interpret zero ROM
    shadow tokens as the actual public bytes. This definition adds no assumptions. -/
def Realizes {Kind : Type} [CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (step : State → State → Prop) (trace : Data p Kind) (initial : State)
    (cells : List Cell) (view : MemoryToken p → MemoryToken p := id) : Prop :=
  ∃ after, Relation.ReflTransGen step initial after ∧
    run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
    ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
      cell.read after = .ok (view sink).word.toBitVec after

/-- Exclude LW-to-x0 from an unchanged-Sail claim. Airbender treats that
    instruction as a NOP, whereas original Sail can perform a failing memory
    access. The explicit Airbender profile covers this deviation separately. -/
def NoDiscardedLoads {Kind : Type} (program : List (ProgramEntry Kind)) : Prop :=
  ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

/-- Bind `trace`'s initial data to the public Sail state `initial` and tracked
    `cells`. `program` is constructed by reading public bytes and running Sail
    decoding, then projecting native metadata with `projection`.

    These are starting-state conditions. Accepted history derives later reads,
    operand bounds and decoder interfaces; callers do not supply those per row. -/
structure NativeInputs {Kind ISA : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime]
    (projection : SailRV32.instruction → Option (DecoderData ISA))
    (trace : Data p Kind) (initial : State) (cells : List Cell)
    (program : List (ProgramEntry ISA)) : Prop where
  /-- The public domain lists each tracked cell once. -/
  distinct : cells.Nodup
  /-- RAM entries are aligned four-byte cells; register cells need no alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Reading the public starting state yields exactly the native seed tokens. -/
  image : initialImage initial cells = some trace.initialMemory
  /-- Sail's initial PC and a public timestamp form the native starting state. -/
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  /-- Public byte reads and actual Sail decoding construct every program entry. -/
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  /-- Only initial clock ranges/alignment are supplied; later clocks are proved. -/
  clocks : ClockBoundary trace

/-- Public machine configuration and address/program domain for the restricted
    arithmetic + word-memory trace. `initial` supplies Sail state and bytes;
    `cells` lists accessible tracked locations. This selects the supported normal
    memory path, without assuming that an instruction's access succeeds. -/
structure PublicBoundary (initial : State) (cells : List Cell)
    (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop where
  /-- All RV32 registers occur in the tracked domain, including x0. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Each public tracked cell appears once. -/
  distinct : cells.Nodup
  /-- Tracked RAM cells are aligned words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Tracked RAM excludes the platform's special MMIO windows. -/
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  /-- Public CSR/PMA/PMP settings select the supported Machine memory path. -/
  configuration : FlatMemoryConfiguration initial
  /-- The restricted program is fetched from public bytes and decoded by Sail. -/
  programImage : ∃ addresses, Trace.programImageWith projection initial addresses = some program
  /-- Instruction addresses lie in public ROM and are aligned to four bytes. -/
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

/-- Add physical memory, initial PC/clock and modeled-table binding to
    `PublicBoundary`. Here `trace.initialMemory` contains actual Sail cell values,
    including ROM bytes. Native zero ROM shadow tokens use `NativeBootBoundary`. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends PublicBoundary initial cells program projection where
  /-- Seed tokens contain the actual starting GPR and physical RAM/ROM values. -/
  image : initialImage initial cells = some trace.initialMemory
  /-- Bind the native starting PC and timestamp to the public state. -/
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  /-- Bind the modeled word-ROM table to these public physical values. -/
  rom : trace.rom = ROM.table cells trace.initialMemory
  /-- Supply the public initial-clock conditions needed by native matching. -/
  clocks : ClockBoundary trace

end Airbender.Trace
