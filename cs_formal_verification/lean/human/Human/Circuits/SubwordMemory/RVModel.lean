module
public import Human.Circuits.SubwordMemory.Artifact
public import Human.Circuits.SubwordMemory.Output
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.ISA.RV32

@[expose] public section

/-! RV32 vocabulary for the LB/LBU/LH/LHU/SB/SH circuit (RV registers, an `RV.State` pre-state
    and the instruction `RV.decode` of the public program entry). `Output` is the aligned cell address, transferred
    word and next PC. There is no MMIO and no configuration in the RV memory map, so no memory-map or configuration
    premise is needed. -/

namespace Airbender.SubwordMemory
open Arithmetic Trace

/-- The circuit's input in RV32 terms: operation (store when `store`, byte when `byte`, sign-extending load when
    `signed`), operand words, start PC, register indices, the original 12-bit immediate and the row's pre-state.
    `readData` is the aligned RAM word on loads, rs2 on stores and unused on ROM loads; `oldData` is the cell before
    a store. -/
structure RVInput where
  store : Bool
  byte : Bool
  signed : Bool
  source : Word
  immediate : Word
  readData : Word
  oldData : Word
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  rd : RV.Reg
  encodedImmediate : BitVec 12
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding): a 1-byte (`byte`)
    or 2-byte access; loads sign-extend when `signed`. -/
def rvInstruction (input : RVInput) : RV.Instr :=
  if input.store then .store (if input.byte then 1 else 2) input.rs2 input.rs1 (input.encodedImmediate.signExtend 32)
  else .load (if input.byte then 1 else 2) input.signed input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : input.source.lo = (w 19).val
  sourceHi : input.source.hi = (w 20).val
  immediateLo : input.immediate.lo = (w 8).val
  immediateHi : input.immediate.hi = (w 9).val
  readLo : input.readData.lo = (w 25).val
  readHi : input.readData.hi = (w 26).val
  oldLo : input.store = true → input.oldData.lo = (w 31).val
  oldHi : input.store = true → input.oldData.hi = (w 32).val
  cellLo : output.cell.lo = (if input.store then w 27 else w 21).val
  cellHi : output.cell.hi = (if input.store then w 28 else w 22).val
  rs1Index : w 5 = (input.rs1.toNat : ZMod p)
  rs2Index : w 6 = (input.rs2.toNat : ZMod p)
  rdIndex : w 7 = (input.rd.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.data.lo = (w 33).val
  outputHi : output.data.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

end Airbender.SubwordMemory
