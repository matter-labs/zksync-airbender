import Airbender.Review.Helpers.UnifiedReduced.ExecutionInputs
import Airbender.Review.Helpers.Memory.ImportedImage

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

structure BootPublicInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  /-- Each tracked register or aligned RAM word occurs once. -/
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Initial PC/GPR/RAM values follow the pinned boot profile; ROM retains bytes. -/
  profile : InitialProfile initial cells
  /-- Actual initial cell reads succeed, including physical ROM reads. -/
  image : ∃ image : List (MemoryToken p), initialImage initial cells = some image
  /-- Native seed values are zero, independently of physical ROM bytes. -/
  seed : trace.initialMemory = Trace.ROMView.nativeBootImage cells
  /-- Public starting PC zero and native timestamp four. Later clocks are proved. -/
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  /-- Actual public bytes and original Sail decoding construct the program table. -/
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
/-- Actual selected-program setup binding. The byte-image condition binds the
    public program; all table cells and row meanings come from imported data. -/
structure ImportedBootInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop
    extends BootPublicInputsWith projection trace initial cells program where
  setup : trace.rom = Setup.importedTable
  importedImage : Trace.ROM.ImportedImage initial

structure ExecutionPublicInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  /-- All architectural registers have public initialized cells, including x0. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Fetch uses aligned instruction words within the public readonly ROM. -/
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  /-- Public CSR data selects the reviewed Sail memory path. -/
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  /-- Indirect-jump programs disable the experimental landing pad. -/
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd, entry.instruction = .JALR (imm, rs1, rd)) → ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  /-- Native LW-to-x0 is a project NOP; this claim uses unchanged Sail instead. -/
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

/-- Execution inputs selecting the actual complete setup artifact. -/
structure ImportedExecutionInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop
    extends ExecutionPublicInputsWith projection trace initial cells program where
  boot : ImportedBootInputsWith projection trace initial cells program

abbrev ImportedExecutionInputs {p : Nat} [Fact p.Prime] :=
  ImportedExecutionInputsWith (p := p) decoderFields


end Airbender.UnifiedReduced
