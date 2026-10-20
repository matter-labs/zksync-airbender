import Human.Circuits.SubwordMemory.Model

namespace Airbender.SubwordMemory
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Uniform valid-path transport through Sail's platform machinery. These
    obligations concern arbitrary native values, never the circuit's result. -/
structure MemoryAccess (input : Input) : Prop where
  load : input.store = false → ∀ nextPC (value : BitVec (8 * (if input.byte then 1 else 2))),
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
  store : input.store = true → ∀ nextPC (value : BitVec (8 * (if input.byte then 1 else 2))),
    run (SailRV32.Functions.rX_bits input.rs1)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
      .ok input.source.toBitVec { input.before with regs := input.before.regs.insert .nextPC nextPC } →
    run (SailRV32.Functions.vmem_write input.rs1 input.immediate.toBitVec
      (if input.byte then 1 else 2) value (.Store .Data) false false false)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
    run (do
      Sail.writeMemory (size := if input.byte then 1 else 2)
        (input.source.toBitVec + input.immediate.toBitVec) value
      pure (.Ok true))
      { input.before with regs := input.before.regs.insert .nextPC nextPC }

omit [MemoryPlatform SailRV32.exception] in
structure RowWordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : w 19 = (input.source.lo : ZMod p)
  sourceHi : w 20 = (input.source.hi : ZMod p)
  immediateLo : w 8 = (input.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.immediate.hi : ZMod p)
  readLo : w 25 = (input.readData.lo : ZMod p)
  readHi : w 26 = (input.readData.hi : ZMod p)
  oldLo : input.store = true → w 31 = (input.oldData.lo : ZMod p)
  oldHi : input.store = true → w 32 = (input.oldData.hi : ZMod p)
  cellLo : output.cell.lo = (if input.store then w 27 else w 21).val
  cellHi : (if input.store then w 28 else w 22) = (output.cell.hi : ZMod p)
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : w 1 = (input.pc.hi : ZMod p)
  outputLo : output.data.lo = (w 33).val
  outputHi : output.data.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

omit [MemoryPlatform SailRV32.exception] in
def rowCircuitModel {p : Nat} [Fact p.Prime] (program : Nat → BitVec 32) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (Verification.subwordTable program))
  represents := fun input output w => RowWordMapping input output w

/-- RAM/ROM loads and RAM stores. Cell/PC/result bounds and halfword alignment are proved
    locally. Input bounds, decoder choices and native transport remain interfaces;
    memory reads are tied to the source-computed address, not a witness output. -/
structure RowInterfaces {p : Nat} (program : Nat → BitVec 32) (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w 10 = if input.store then 1 else 0
  byteSelection : w 11 = if input.byte then 1 else 0
  signedSelection : w 12 = if input.signed then 1 else 0
  sourceBound : input.source.Bounded
  immediateBound : input.immediate.Bounded
  readDataBound : 64 ≤ output.cell.hi → input.readData.Bounded
  oldDataBound : input.store = true → input.oldData.Bounded
  initialPCBound : input.pc.Bounded
  cellHighBound : output.cell.hi < limbBase
  sourceRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.source.toBitVec input.before
  storeRead : input.store = true → run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.readData.toBitVec input.before
  loadRead : input.store = false → 64 ≤ output.cell.hi → readBytes (ue := SailRV32.exception) 4
    ((input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4) input.before =
    .ok input.readData.toBitVec input.before
  -- Only this row's ROM load needs a connection to the fixed program image.
  romImage : input.store = false → output.cell.hi < 64 →
    readBytes (ue := SailRV32.exception) 4 output.cell.toBitVec.toNat input.before =
      .ok (program (output.cell.value / 4)) input.before
  oldRead : input.store = true → readBytes (ue := SailRV32.exception) 4
    ((input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4) input.before =
    .ok input.oldData.toBitVec input.before
  signExtension : input.immediate.toBitVec =
    SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before
  memory : MemoryAccess input

end Airbender.SubwordMemory
