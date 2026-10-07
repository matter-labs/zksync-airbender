import Airbender.Review.SubwordMemory.Artifact
import Airbender.Review.SubwordTables
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.SubwordMemory
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- The original LB/LBU/LH/LHU operands and native pre-state. `readData` is the
    aligned four-byte RAM word, fixed independently of the circuit witness. -/
structure Input where
  byte : Bool
  signed : Bool
  source : Word
  immediate : Word
  readData : Word
  pc : Word
  rs1 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

structure Output where
  cell : Word
  data : Word
  pc : Word

variable [MemoryPlatform SailRV32.exception]

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  SailRV32.Functions.execute_LOAD input.encodedImmediate input.rs1 input.rd
    (!input.signed) (if input.byte then 1 else 2)

/-- Correct aligned read address and complete native register/PC effects. Sail
    supplies extraction and extension; there is no local instruction spec. -/
def spec (input : Input) (output : Output) : Prop :=
  output.cell.toBitVec.toNat =
    (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
  Sail.stepSpec input.before (execution input) input.rd ⟨output.data, output.pc⟩

omit [MemoryPlatform SailRV32.exception] in
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : w 19 = (input.source.lo : ZMod p)
  sourceHi : w 20 = (input.source.hi : ZMod p)
  immediateLo : w 8 = (input.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.immediate.hi : ZMod p)
  readLo : w 25 = (input.readData.lo : ZMod p)
  readHi : w 26 = (input.readData.hi : ZMod p)
  cellLo : output.cell.lo = (w 21).val
  cellHi : w 22 = (output.cell.hi : ZMod p)
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : w 1 = (input.pc.hi : ZMod p)
  outputLo : output.data.lo = (w 33).val
  outputHi : output.data.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

omit [MemoryPlatform SailRV32.exception] in
def circuitModel {p : Nat} [Fact p.Prime] (program : Nat → BitVec 32) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (Verification.subwordTable program))
  represents := fun input output w => WordMapping input output w

/-- RAM loads only. Low cell/PC/result bounds and halfword alignment are proved
    from the artifact. Input bounds, decoder choices and native transport remain
    interfaces. Neither memory premise mentions the circuit's result data. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  load : w 10 = 0
  byteSelection : w 11 = if input.byte then 1 else 0
  signedSelection : w 12 = if input.signed then 1 else 0
  ramAddress : 64 ≤ output.cell.hi
  sourceBound : input.source.Bounded
  immediateBound : input.immediate.Bounded
  readDataBound : input.readData.Bounded
  initialPCBound : input.pc.Bounded
  cellHighBound : output.cell.hi < limbBase
  sourceRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.source.toBitVec input.before
  loadRead : readBytes (ue := SailRV32.exception) 4
    ((input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4) input.before =
    .ok input.readData.toBitVec input.before
  signExtension : input.immediate.toBitVec =
    SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before
  memory : ∀ nextPC (value : BitVec (8 * (if input.byte then 1 else 2))),
    run (SailRV32.Functions.rX_bits input.rs1)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
      .ok input.source.toBitVec { input.before with regs := input.before.regs.insert .nextPC nextPC } →
    (readBytes (ue := SailRV32.exception) (if input.byte then 1 else 2)
      (input.source.toBitVec + input.immediate.toBitVec).toNat).run input.before =
      .ok value input.before →
    run (SailRV32.Functions.vmem_read input.rs1 input.immediate.toBitVec
      (if input.byte then 1 else 2) (.Load .Data) false false false)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
      .ok (.Ok value) { input.before with regs := input.before.regs.insert .nextPC nextPC }

end Airbender.SubwordMemory
