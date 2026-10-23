import Airbender.Review.Helpers.Context.InitializationInputs
import Airbender.Review.Helpers.Context.InitializationUnifiedInputs
import Airbender.Review.Helpers.Context.Registries.SubwordMemoryInputs
import Airbender.Review.Helpers.UnifiedReduced.ImportedInputs
import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Review.Circuits.SubwordMemory.Model
import Airbender.Proofs.UnifiedReduced.WordMemorySoundness
import Airbender.Proofs.UnifiedReduced.ROMSoundness
import Airbender.Proofs.UnifiedReduced.MemoryExecution
import Airbender.Proofs.UnifiedReduced.MixedRAMRetirement
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.AddSub.ModularComposition
import Airbender.Proofs.AddSub.ModularExternalExecution
import Airbender.Review.Helpers.UnifiedReduced.Modular
import Airbender.Review.Helpers.UnifiedReduced.RetirementProfile

/-! Compatibility regressions for old public claim premises and profile fields
under upstream device routing, retaining arbitrary original Sail handlers. These
constructive adapters do not assert raw declaration-type identity. -/
namespace Airbender.PlatformCompatibilityPreparation
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

example (handlers : MemoryPlatform SailRV32.exception) :
    handlers.upstream.terminalWrite = handlers.terminalWrite := rfl
example (handlers : MemoryPlatform SailRV32.exception) :
    handlers.upstream.reserve = handlers.reserve := rfl
example (handlers : MemoryPlatform SailRV32.exception) :
    handlers.upstream.reservationMatches = handlers.reservationMatches := rfl
example (handlers : MemoryPlatform SailRV32.exception) (address : BitVec 32) :
    @PlatformWordAddress handlers.upstream address ↔ OrdinaryWordAddress address :=
  ordinaryWordAddress_upstream address
end Airbender.PlatformCompatibilityPreparation

section
variable [handlers : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
local instance : _root_.Sail.ArchSem.MemoryPlatform SailRV32.exception := handlers.upstream
set_option warningAsError true
set_option Elab.async false

namespace Airbender.UnifiedReduced.WordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_row_soundness_from_history [Fact p.Prime]
    (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {initial : State} {cells : List Cell} {events : List MemoryAccess}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    {after : State} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w importedConstraintsTraceColumns.execute = 1)
    (past : SailHistory cells events (retiredState initial input.pc.toBitVec) input.before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (sourceRange : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (configuration : FlatMemoryConfiguration initial)
    (aligned : ∀ address, Cell.ram address ∈ cells → address.toNat % 4 = 0)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before) :
    Airbender.WordMemory.spec input output := by
  exact row_soundness_from_history
    hp core active past history sourceRange words fields query encoding configuration aligned
    (fun address present => ordinaryWordAddress_for (ordinary address present)) destination copiedWord
    pcRead

end Airbender.UnifiedReduced.WordMemory.Proofs

namespace Airbender.UnifiedReduced.WordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_row_soundness_from_memory [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (memory : MemoryExecution trace initial cells)
    (initialization : NativeInputs projection trace initial cells program)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec) :
    Airbender.WordMemory.spec input output := by
  exact row_soundness_from_memory
    hp inverse accepted member words position source query encoding memory initialization configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) destination copiedWord

end Airbender.UnifiedReduced.WordMemory.Proofs

namespace Airbender.UnifiedReduced.WordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_row_soundness [Fact p.Prime]
    (hp : FieldCapacity.ClockNoWrap p timestampBase) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (accepted : Accepted trace) (decoded : Decoded trace program)
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (mapping : TraceMapping trace initial cells program input output w)
    (initialization : NativeInputs decoderFields trace initial cells program)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (copiedWord : output.data.toBitVec = input.readData.toBitVec) :
    Airbender.WordMemory.spec input output := by
  exact row_soundness
    hp inverse accepted decoded member mapping initialization configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) destination copiedWord

end Airbender.UnifiedReduced.WordMemory.Proofs

namespace Airbender.UnifiedReduced.WordMemory.NativeROM.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_soundness_from_memory [Fact p.Prime]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (boot : BootInputsWith projection trace initial cells program)
    (accepted : Accepted trace) (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    (words : UnifiedReduced.WordMemory.WordMapping input output w)
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister) :
    Airbender.WordMemory.spec input output := by
  exact soundness_from_memory
    hp inverse boot accepted memory member words position source query encoding configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) destination

end Airbender.UnifiedReduced.WordMemory.NativeROM.Proofs

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_word_execution_from_memory [Fact p.Prime]
    (hp : FieldCapacity.NativeRomCapacity p) (inverse : SerializedInverse.Clock p)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (accepted : Accepted trace)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ (ROMView.data initial trace).rows)
    {before after : State} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {entry : ProgramEntry}
    (boot : BootInputsWith projection trace initial cells program)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (words : WordMemory.WordMapping input output w)
    (atRow : input.before = retiredState before (Control.initialPC w).toBitVec)
    (position : RowPosition (ROMView.data initial trace) initial cells ⟨.machine, w⟩ input.before)
    (source : entry.SourceWith initial decoderFields)
    (memory : MemoryExecution (ROMView.data initial trace) initial cells)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4))
    (history : SailHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Control.initialPC w).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Control.finalPC w).toBitVec) := by
  exact word_execution_from_memory
    hp inverse accepted member boot configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) destination words atRow
    position source memory query encoding history

end Airbender.UnifiedReduced.Proofs

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_mixed_ram_cycle_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  exact mixed_ram_cycle_at
    accepted inputs effects permutation order history configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) ram destination member words
    instruction

end Airbender.UnifiedReduced.Caller.Proofs

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_mixed_ram_cycle
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map transferEvent) ∧
      SailHistory cells events initial finalState ∧
      RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  exact mixed_ram_cycle
    accepted inputs started configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) ram destination member words
    instruction

end Airbender.UnifiedReduced.Caller.Proofs

namespace Airbender.UnifiedReduced
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_Caller_ram_cycle_soundness
    {data : Caller.RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : Reference.RiscV.Sail.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell}
    (accepted : Caller.MixedMemoryAccepted data program)
    (inputs : Caller.MixedMemoryInputs data program initial ca oa cells)
    (started : 0 < (Trace.timeOfPair data.machine.initial.timestamp).value)
    (configuration : Reference.RiscV.Sail.FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Trace.Cell.ram address ∈ cells → Reference.RiscV.Sail.OrdinaryWordAddress address)
    (ram : ∀ address, Trace.Cell.ram address ∈ cells → 4194304 ≤ address.toNat)
    {w : Nat → ZMod babyBearModulus} {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output}
    (destination : input.store = false → input.rd ≠ Reference.RiscV.Sail.zeroRegister)
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) ∈ data.machine.rows)
    (words : WordMemory.WordMapping input output w)
    (instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
      entry.instruction = if input.store then .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
        else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)) :
    ∃ events finalState,
      events.Perm (data.mixedSteps.map Trace.transferEvent) ∧
      Trace.SailHistory cells events initial finalState ∧
      Caller.RetiresCycle cells events initial finalState (⟨.machine, w⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)
        (Airbender.WordMemory.execution input) := by
  exact Caller.ram_cycle_soundness
    accepted inputs started configuration
    (fun address present => ordinaryWordAddress_for (ordinary address present)) ram destination member words
    instruction

end Airbender.UnifiedReduced

namespace Airbender.AddSub.Modular.Pooled.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_row_step
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (memoryConfiguration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program)
    (terminal : trace.terminal.word.Bounded)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    StepWith Pooled.decoderFields Pooled.clauseFor program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  exact row_step
    hp inverse accepted clocks image wordSetup subwordSetup registers aligned
    (fun address present => ordinaryWordAddress_for (ordinary address present)) memoryConfiguration
    programImage decoded code loads terminal isa configuration member native past history

end Airbender.AddSub.Modular.Pooled.Proofs

namespace Airbender.AddSub.Modular.External.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

/-- Exact old ordinary-address premise with arbitrary original handlers. -/
theorem upstream_old_row_step
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (memoryConfiguration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : External.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program) (terminal : trace.terminal.word.Bounded)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    {stream : List (BitVec 32)} (ports : External.StreamPorts trace stream)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    External.Step stream program
      (retiredState before row.start.word.toBitVec, External.readIndex trace row)
      (retiredState after row.finish.word.toBitVec,
        External.readIndex trace row + if External.isRead row then 1 else 0) := by
  exact row_step
    hp inverse accepted clocks image wordSetup subwordSetup registers aligned
    (fun address present => ordinaryWordAddress_for (ordinary address present)) memoryConfiguration
    programImage decoded code loads terminal isa configuration ports member native past history

end Airbender.AddSub.Modular.External.Proofs

namespace Airbender.PlatformCompatibilityPreparation
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

/-- The genuine old field contract, assembled under the original handlers'
upstream routing. Only the ordinary-domain field is translated. -/
theorem execution_inputs_with_from_old_fields {p : Nat} [Fact p.Prime]
    (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (boot : UnifiedReduced.BootInputsWith projection trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
      entry.instruction = .JALR (imm, rs1, rd)) →
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)) :
    UnifiedReduced.ExecutionInputsWith projection trace initial cells program := by
  exact {
    boot := boot,
    registers := registers,
    code := code,
    configuration := configuration,
    ordinary := fun address member => ordinaryWordAddress_for (ordinary address member),
    landingPadDisabled := landingPadDisabled,
    loads := loads }

/-- The old mixed alias has exactly the same old fields and registry. -/
theorem mixed_inputs_from_old_fields {p : Nat} [Fact p.Prime]
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (boot : UnifiedReduced.BootInputsWith UnifiedReduced.Mixed.decoderFields trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
      entry.instruction = .JALR (imm, rs1, rd)) →
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)) :
    UnifiedReduced.Mixed.Inputs trace initial cells program :=
  execution_inputs_with_from_old_fields (handlers := handlers) UnifiedReduced.Mixed.decoderFields
    boot registers code configuration ordinary landingPadDisabled loads

/-- The old modular alias has exactly the same old fields and registry. -/
theorem modular_inputs_from_old_fields {p : Nat} [Fact p.Prime]
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (boot : UnifiedReduced.BootInputsWith UnifiedReduced.Modular.decoderFields trace initial cells program)
    (registers : ∀ index, Cell.register index ∈ cells)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
      entry.instruction = .JALR (imm, rs1, rd)) →
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)) :
    UnifiedReduced.Modular.Inputs trace initial cells program :=
  execution_inputs_with_from_old_fields (handlers := handlers) UnifiedReduced.Modular.decoderFields
    boot registers code configuration ordinary landingPadDisabled loads

/-- The old caller retirement profile retains code/register/configuration,
JALR/load restrictions and every handler, translating only ordinary addresses. -/
theorem caller_retirement_from_old_fields {p : Nat} [Fact p.Prime]
    {data : UnifiedReduced.Caller.RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell}
    (code : UnifiedReduced.Caller.CodeProfile data program cells)
    (registers : ∀ index, Cell.register index ∈ cells)
    (configuration : FlatMemoryConfiguration initial)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
      entry.instruction = .JALR (imm, rs1, rd)) →
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    (loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)) :
    UnifiedReduced.Caller.RetirementProfile data program initial cells := by
  exact {
    code := code,
    registers := registers,
    configuration := configuration,
    ordinary := fun address member => ordinaryWordAddress_for (ordinary address member),
    landingPadDisabled := landingPadDisabled,
    loads := loads }

end Airbender.PlatformCompatibilityPreparation

namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldExecutionInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  boot : BootInputsWith projection trace initial cells program
  registers : ∀ index, Cell.register index ∈ cells
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd, entry.instruction = .JALR (imm, rs1, rd)) → ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.UnifiedReduced

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldPublicBoundary (initial : State) (cells : List Cell)
    (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop where
  registers : ∀ index, Cell.register index ∈ cells
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  programImage : ∃ addresses, Trace.programImageWith projection initial addresses = some program
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

end Airbender.Trace

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends CompatibilityOldPublicBoundary initial cells program projection where
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  rom : trace.rom = ROM.table cells trace.initialMemory
  clocks : ClockBoundary trace

end Airbender.Trace

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldNativeBootBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends CompatibilityOldPublicBoundary before cells program projection where
  profile : InitialProfile before cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initial : trace.initial = PCState.boundary 0 (4, 0)
  rom : ∃ image, initialImage before cells = some image ∧ trace.rom = ROM.table cells image

end Airbender.Trace

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldPooledPublicInputs (initial : State) (cells : List Cell)
    (program : List PooledProgramEntry) : Prop where
  registers : ∀ index, Cell.register index ∈ cells
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  loads : NoDiscardedLoads program

end Airbender.Trace

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldPooledInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (projection : SailRV32.instruction → Option (DecoderData PooledFamily) := pooledDecoderFields) : Prop
    extends NativeInputs projection trace initial cells program,
      CompatibilityOldPooledPublicInputs initial cells program where
  wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  verifierBoundary : VerifierBoundary.Closure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

end Airbender.Trace

namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldPooledBootInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (projection : SailRV32.instruction → Option (DecoderData PooledFamily) := pooledDecoderFields) : Prop
    extends CompatibilityOldPooledPublicInputs initial cells program where
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  profile : InitialProfile initial cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ image, initialImage initial cells = some image ∧
    trace.rom.wordMemory = ROM.table cells image
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  verifierBoundary : VerifierBoundary.BootClosure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

end Airbender.Trace

namespace Airbender.WordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends PooledHistoryInputs trace initial cells program where
  ordinary : ∀ address, Cell.ram address ∈ cells → Sail.OrdinaryWordAddress address
  configuration : Sail.FlatMemoryConfiguration initial

end Airbender.WordMemory

namespace Airbender.SubwordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends PooledHistoryInputs trace initial cells program where
  ordinary : ∀ address, Cell.ram address ∈ cells → Sail.OrdinaryWordAddress address
  configuration : Sail.FlatMemoryConfiguration initial

end Airbender.SubwordMemory

namespace Airbender.SubwordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldRAMInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) : Prop
    extends NativeInputs decoderFields trace initial cells program where
  configuration : FlatMemoryConfiguration initial
  ramDomain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  setup : ∃ values, trace.rom = Verification.subwordTable values

end Airbender.SubwordMemory

namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldExecutionPublicInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  registers : ∀ index, Cell.register index ∈ cells
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd, entry.instruction = .JALR (imm, rs1, rd)) → ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldImportedExecutionInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop
    extends CompatibilityOldExecutionPublicInputsWith projection trace initial cells program where
  boot : ImportedBootInputsWith projection trace initial cells program

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

abbrev CompatibilityOldImportedExecutionInputs {p : Nat} [Fact p.Prime] :=
  CompatibilityOldImportedExecutionInputsWith (p := p) decoderFields

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

abbrev CompatibilityOldExecutionInputs {p : Nat} [Fact p.Prime] := CompatibilityOldExecutionInputsWith (p := p) decoderFields

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced.WordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldInterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Airbender.WordMemory.Input) (_output : Airbender.WordMemory.Output)
    (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat
  destination : input.store = false → input.rd ≠ zeroRegister

end Airbender.UnifiedReduced.WordMemory

namespace Airbender.UnifiedReduced.WordMemory.NativeROM
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

structure CompatibilityOldInterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Airbender.WordMemory.Input) (_output : Airbender.WordMemory.Output)
    (_w : Nat → ZMod p) : Prop where
  boot : BootInputs trace initial cells program
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  destination : input.store = false → input.rd ≠ zeroRegister

end Airbender.UnifiedReduced.WordMemory.NativeROM

namespace Airbender.Initialization
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

section
variable {p : Nat} [Fact p.Prime]
structure CompatibilityOldPooledProfile (base : PooledTrace p) (layout : Layout)
    (geometry : Geometry layout) (windows : Windows layout)
    (initial : State) (program : List PooledProgramEntry) : Prop where
  ordinary : ∀ address, Cell.ram address ∈ cells geometry windows → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  loads : NoDiscardedLoads program
  programImage : ∃ addresses, programImageRunWith pooledDecoderFields initial addresses = some program
  profile : InitialProfile initial (cells geometry windows)
  initialBoundary : base.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ image, initialImage initial (cells geometry windows) = some image ∧
    base.rom.wordMemory = ROM.table (cells geometry windows) image
  subwordSetup : base.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  verifierBoundary : VerifierBoundary.BootClosure base.initial
    (base.rows.map Row.start) (base.rows.map Row.finish)
end

end Airbender.Initialization

namespace Airbender.Initialization
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

section
variable {p : Nat} [Fact p.Prime]
structure CompatibilityOldUnifiedProfile (base : UnifiedTrace p) (layout : Layout)
    (geometry : Geometry layout) (windows : Windows layout)
    (initial : State) (program : List UnifiedReduced.ProgramEntry) : Prop where
  profile : InitialProfile initial (cells geometry windows)
  image : ∃ image : List (MemoryToken p), initialImage initial (cells geometry windows) = some image
  initialPC : base.initial = PCState.boundary 0 (4, 0)
  programImage : ∃ addresses,
    programImageRunWith UnifiedReduced.decoderFields initial addresses = some program
  setup : base.rom = UnifiedReduced.Setup.table initial
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells geometry windows → OrdinaryWordAddress address
  landingPadDisabled : (∃ entry ∈ program, ∃ imm rs1 rd,
    entry.instruction = .JALR (imm, rs1, rd)) → ∃ security,
    initial.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0
  loads : ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)
end

end Airbender.Initialization


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_public_boundary {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option DecoderData}
    (old : CompatibilityOldPublicBoundary initial cells program projection) :
    PublicBoundary initial cells program projection := by
  exact {
    registers := old.registers,
    distinct := old.distinct,
    aligned := old.aligned,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    configuration := old.configuration,
    programImage := old.programImage,
    code := old.code }

end Airbender.Trace


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_execution_boundary {p : Nat} [Fact p.Prime] {trace : Data p}
    {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option DecoderData}
    (old : CompatibilityOldExecutionBoundary trace initial cells program projection) :
    ExecutionBoundary trace initial cells program projection := by
  exact {
    toPublicBoundary := compatibility_upstream_public_boundary (handlers := handlers) old.toCompatibilityOldPublicBoundary,
    image := old.image,
    initialPC := old.initialPC,
    rom := old.rom,
    clocks := old.clocks }

end Airbender.Trace


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_native_boot_boundary {p : Nat} [Fact p.Prime] {trace : Data p}
    {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option DecoderData}
    (old : CompatibilityOldNativeBootBoundary trace initial cells program projection) :
    NativeBootBoundary trace initial cells program projection := by
  exact {
    toPublicBoundary := compatibility_upstream_public_boundary (handlers := handlers) old.toCompatibilityOldPublicBoundary,
    profile := old.profile,
    seed := old.seed,
    initial := old.initial,
    rom := old.rom }

end Airbender.Trace


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_pooled_public_inputs {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (old : CompatibilityOldPooledPublicInputs initial cells program) :
    PooledPublicInputs initial cells program := by
  exact {
    registers := old.registers,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    configuration := old.configuration,
    landingPadDisabled := old.landingPadDisabled,
    code := old.code,
    loads := old.loads }

end Airbender.Trace


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_pooled_inputs {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    (old : CompatibilityOldPooledInputs trace initial cells program projection) :
    PooledInputs trace initial cells program projection := by
  exact {
    toNativeInputs := old.toNativeInputs,
    toPooledPublicInputs := compatibility_upstream_pooled_public_inputs (handlers := handlers) old.toCompatibilityOldPooledPublicInputs,
    wordSetup := old.wordSetup,
    subwordSetup := old.subwordSetup,
    verifierBoundary := old.verifierBoundary }

end Airbender.Trace


namespace Airbender.Trace
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_pooled_boot_inputs {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    (old : CompatibilityOldPooledBootInputs trace initial cells program projection) :
    PooledBootInputs trace initial cells program projection := by
  exact {
    toPooledPublicInputs := compatibility_upstream_pooled_public_inputs (handlers := handlers) old.toCompatibilityOldPooledPublicInputs,
    distinct := old.distinct,
    aligned := old.aligned,
    programImage := old.programImage,
    profile := old.profile,
    seed := old.seed,
    initialBoundary := old.initialBoundary,
    physicalImage := old.physicalImage,
    subwordSetup := old.subwordSetup,
    verifierBoundary := old.verifierBoundary }

end Airbender.Trace


namespace Airbender.WordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_interface {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (old : CompatibilityOldInterfaceAssumptions trace initial cells program) :
    InterfaceAssumptions trace initial cells program := by
  exact {
    toPooledHistoryInputs := old.toPooledHistoryInputs,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    configuration := old.configuration }

end Airbender.WordMemory


namespace Airbender.SubwordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_interface {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (old : CompatibilityOldInterfaceAssumptions trace initial cells program) :
    InterfaceAssumptions trace initial cells program := by
  exact {
    toPooledHistoryInputs := old.toPooledHistoryInputs,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    configuration := old.configuration }

end Airbender.SubwordMemory


namespace Airbender.SubwordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_ram_inputs {p : Nat} [Fact p.Prime] {trace : NativeTrace p}
    {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (old : CompatibilityOldRAMInputs trace initial cells program) :
    RAMInputs trace initial cells program := by
  exact {
    toNativeInputs := old.toNativeInputs,
    configuration := old.configuration,
    ramDomain := old.ramDomain,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    code := old.code,
    setup := old.setup }

end Airbender.SubwordMemory


namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_execution_public_inputs {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (old : CompatibilityOldExecutionPublicInputsWith projection trace initial cells program) :
    ExecutionPublicInputsWith projection trace initial cells program := by
  exact {
    registers := old.registers,
    code := old.code,
    configuration := old.configuration,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    landingPadDisabled := old.landingPadDisabled,
    loads := old.loads }

end Airbender.UnifiedReduced


namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_imported_execution_inputs_with {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell}
    {program : List UnifiedReduced.ProgramEntry}
    (old : CompatibilityOldImportedExecutionInputsWith projection trace initial cells program) :
    ImportedExecutionInputsWith projection trace initial cells program := by
  exact {
    toExecutionPublicInputsWith := compatibility_upstream_execution_public_inputs (handlers := handlers) old.toCompatibilityOldExecutionPublicInputsWith,
    boot := old.boot }

end Airbender.UnifiedReduced


namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_imported_execution_inputs {p : Nat} [Fact p.Prime] {trace : UnifiedTrace p}
    {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (old : CompatibilityOldImportedExecutionInputs trace initial cells program) :
    ImportedExecutionInputs trace initial cells program :=
  compatibility_upstream_imported_execution_inputs_with (handlers := handlers) old

end Airbender.UnifiedReduced


namespace Airbender.UnifiedReduced
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_execution_inputs {p : Nat} [Fact p.Prime] {trace : UnifiedTrace p}
    {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (old : CompatibilityOldExecutionInputs trace initial cells program) :
    ExecutionInputs trace initial cells program :=
  PlatformCompatibilityPreparation.execution_inputs_with_from_old_fields (handlers := handlers) decoderFields
    old.boot old.registers old.code old.configuration old.ordinary old.landingPadDisabled old.loads

end Airbender.UnifiedReduced


namespace Airbender.UnifiedReduced.WordMemory
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_interface {p : Nat} [Fact p.Prime] {trace : UnifiedTrace p}
    {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (old : CompatibilityOldInterfaceAssumptions trace initial cells program input output w) :
    InterfaceAssumptions trace initial cells program input output w := by
  exact {
    initialization := old.initialization,
    configuration := old.configuration,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    ram := old.ram,
    destination := old.destination }

end Airbender.UnifiedReduced.WordMemory


namespace Airbender.UnifiedReduced.WordMemory.NativeROM
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_interface {p : Nat} [Fact p.Prime] {trace : UnifiedTrace p}
    {initial : State} {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    {input : Airbender.WordMemory.Input} {output : Airbender.WordMemory.Output} {w : Nat → ZMod p}
    (old : CompatibilityOldInterfaceAssumptions trace initial cells program input output w) :
    InterfaceAssumptions trace initial cells program input output w := by
  exact {
    boot := old.boot,
    configuration := old.configuration,
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    destination := old.destination }

end Airbender.UnifiedReduced.WordMemory.NativeROM


namespace Airbender.Initialization
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

section
variable {p : Nat} [Fact p.Prime]
/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_pooled_profile {base : PooledTrace p} {layout : Layout}
    {geometry : Geometry layout} {windows : Windows layout}
    {initial : State} {program : List PooledProgramEntry}
    (old : CompatibilityOldPooledProfile base layout geometry windows initial program) :
    PooledProfile base layout geometry windows initial program := by
  exact {
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    configuration := old.configuration,
    landingPadDisabled := old.landingPadDisabled,
    code := old.code,
    loads := old.loads,
    programImage := old.programImage,
    profile := old.profile,
    initialBoundary := old.initialBoundary,
    physicalImage := old.physicalImage,
    subwordSetup := old.subwordSetup,
    verifierBoundary := old.verifierBoundary }

end

end Airbender.Initialization


namespace Airbender.Initialization
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail

section
variable {p : Nat} [Fact p.Prime]
/-- Same old fields and arbitrary original handlers; only ordinary-domain
or the previously translated parent profile changes representation. -/
theorem compatibility_upstream_unified_profile {base : UnifiedTrace p} {layout : Layout}
    {geometry : Geometry layout} {windows : Windows layout}
    {initial : State} {program : List UnifiedReduced.ProgramEntry}
    (old : CompatibilityOldUnifiedProfile base layout geometry windows initial program) :
    UnifiedProfile base layout geometry windows initial program := by
  exact {
    ordinary := fun address member => ordinaryWordAddress_for (old.ordinary address member),
    profile := old.profile,
    image := old.image,
    initialPC := old.initialPC,
    programImage := old.programImage,
    setup := old.setup,
    code := old.code,
    configuration := old.configuration,
    landingPadDisabled := old.landingPadDisabled,
    loads := old.loads }

end

end Airbender.Initialization

end
