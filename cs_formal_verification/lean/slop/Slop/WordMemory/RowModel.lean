import Human.Circuits.WordMemory.Model

namespace Airbender.WordMemory
open Airbender.Arithmetic Airbender.Reference.RiscV Airbender.Reference.Sail
open _root_.Sail.ArchSem Variables

-- Internal row-calculation obligations, discharged by initialized trace history.
/-- A successful RAM path through Sail's address translation/access machinery.
    These uniform transport obligations do not mention circuit outputs. They
    remain to be discharged from the platform configuration and memory interface. -/
structure MemoryAccess (input : Input) : Prop where
  load : input.store = false → ∀ nextPC value,
    run (SailRV32.Functions.rX_bits input.rs1)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
        .ok input.source.toBitVec { input.before with regs := input.before.regs.insert .nextPC nextPC } →
    readBytes (ue := SailRV32.exception) 4
      (input.source.toBitVec + input.immediate.toBitVec).toNat
      input.before = .ok value input.before →
    run (SailRV32.Functions.vmem_read input.rs1 input.immediate.toBitVec 4
      (.Load .Data) false false false)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
        .ok (.Ok value) { input.before with regs := input.before.regs.insert .nextPC nextPC }
  store : input.store = true → ∀ nextPC value,
    run (SailRV32.Functions.rX_bits input.rs1)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
        .ok input.source.toBitVec { input.before with regs := input.before.regs.insert .nextPC nextPC } →
    run (SailRV32.Functions.vmem_write input.rs1 input.immediate.toBitVec 4 value
      (.Store .Data) false false false)
      { input.before with regs := input.before.regs.insert .nextPC nextPC } =
    run (do
      Sail.writeMemory (size := 4) (input.source.toBitVec + input.immediate.toBitVec) value
      pure (.Ok true))
      { input.before with regs := input.before.regs.insert .nextPC nextPC }

structure RowWordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : w Variables.sourceLo = (input.source.lo : ZMod p)
  sourceHi : w Variables.sourceHi = (input.source.hi : ZMod p)
  immediateLo : w Variables.immediateLo = (input.immediate.lo : ZMod p)
  immediateHi : w Variables.immediateHi = (input.immediate.hi : ZMod p)
  readLo : w readDataLo = (input.readData.lo : ZMod p)
  readHi : w readDataHi = (input.readData.hi : ZMod p)
  addressLo : (if input.store then w writeAddressLo else w readAddressLo) =
    (output.address.lo : ZMod p)
  addressHi : (if input.store then w writeAddressHi else w readAddressHi) =
    (output.address.hi : ZMod p)
  rs1Index : match input.rs1 with | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w Variables.rdIndex = (bits.toNat : ZMod p)
  pcLo : w initialPCLo = (input.pc.lo : ZMod p)
  pcHi : w initialPCHi = (input.pc.hi : ZMod p)
  outputLo : output.data.lo = (w writeDataLo).val
  outputHi : output.data.hi = (w writeDataHi).val
  finalPCLo : output.pc.lo = (w Variables.finalPCLo).val
  finalPCHi : output.pc.hi = (w Variables.finalPCHi).val

def rowCircuitModel {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints rom)
  represents := fun input output w => RowWordMapping input output w

/-- Bounds, original reads and native memory transport are explicit interfaces;
    address arithmetic, RAM copying/ROM selection and PC+4 are proved. -/
structure RowInterfaces {p : Nat} [Fact p.Prime] (rom : Table (ZMod p) (fields 9))
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  active : w execute = 1
  selected : w storeSelector = if input.store then 1 else 0
  preprocessing : if input.store then input.rd = Sail.zeroRegister
    else input.rs2 = Sail.zeroRegister ∧ input.rd ≠ Sail.zeroRegister
  sourceBound : input.source.Bounded
  immediateBound : input.immediate.Bounded
  readDataBound : 64 ≤ output.address.hi → input.readData.Bounded
  initialPCBound : input.pc.Bounded
  addressBound : output.address.Bounded
  disabledROM : ∀ row, rom.Contains #[] row → row[8] = 0 → row[1] = 0 ∧ row[2] = 0
  -- Uniform program-image binding; it mentions no circuit witness or output.
  romImage : ∀ (address : Word) (lo hi : ZMod p), address.Bounded → address.hi < 64 →
    rom.Contains #[] #v[(address.lo : ZMod p) + 65536 * address.hi,
      lo, hi, 0, 0, 0, 0, 0, 34] →
    readBytes (ue := SailRV32.exception) 4 address.toBitVec.toNat input.before =
      .ok (Word.mk lo.val hi.val).toBitVec input.before
  sourceRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.source.toBitVec input.before
  storeRead : input.store = true → run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.readData.toBitVec input.before
  loadRead : input.store = false → 64 ≤ output.address.hi → readBytes (ue := SailRV32.exception) 4
    (input.source.toBitVec + input.immediate.toBitVec).toNat input.before =
      .ok input.readData.toBitVec input.before
  signExtension : input.immediate.toBitVec =
    SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before
  memory : MemoryAccess input

end Airbender.WordMemory
