module
public import Human.Circuits.SubwordMemory.Artifact
public import Human.Circuits.SubwordMemory.Output
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Context.RVRowModel
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
  /-- Select a store when true and a load when false. -/
  store : Bool
  /-- Select a byte access when true and a halfword access when false. -/
  byte : Bool
  /-- Select sign extension for a load when true. -/
  signed : Bool
  /-- The address-base operand word. -/
  source : Word
  /-- The decoded immediate word. -/
  immediate : Word
  /-- The word read by the circuit port. -/
  readData : Word
  /-- The cell word before a store. -/
  oldData : Word
  /-- The row's starting PC. -/
  pc : Word
  /-- The first source register index. -/
  rs1 : RV.Reg
  /-- The second source register index. -/
  rs2 : RV.Reg
  /-- The destination register index. -/
  rd : RV.Reg
  /-- The original 12-bit immediate encoding. -/
  encodedImmediate : BitVec 12
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding): a 1-byte (`byte`)
    or 2-byte access; loads sign-extend when `signed`. -/
def rvInstruction (input : RVInput) : RV.Instr :=
  if input.store then .store (if input.byte then 1 else 2) input.rs2 input.rs1 (input.encodedImmediate.signExtend 32)
  else .load (if input.byte then 1 else 2) input.signed input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the address-base operand to its witness column. -/
  sourceLo : input.source.lo = (w 19).val
  /-- Bind the high limb of the address-base operand to its witness column. -/
  sourceHi : input.source.hi = (w 20).val
  /-- Bind the low limb of the decoded immediate to its witness column. -/
  immediateLo : input.immediate.lo = (w 8).val
  /-- Bind the high limb of the decoded immediate to its witness column. -/
  immediateHi : input.immediate.hi = (w 9).val
  /-- Bind the low limb of the read-port word to its witness column. -/
  readLo : input.readData.lo = (w 25).val
  /-- Bind the high limb of the read-port word to its witness column. -/
  readHi : input.readData.hi = (w 26).val
  /-- Bind the low limb of the cell word before a store to its witness column. -/
  oldLo : input.store = true → input.oldData.lo = (w 31).val
  /-- Bind the high limb of the cell word before a store to its witness column. -/
  oldHi : input.store = true → input.oldData.hi = (w 32).val
  /-- Bind the low limb of the aligned cell address to its witness column. -/
  cellLo : output.cell.lo = (if input.store then w 27 else w 21).val
  /-- Bind the high limb of the aligned cell address to its witness column. -/
  cellHi : output.cell.hi = (if input.store then w 28 else w 22).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : w 5 = (input.rs1.toNat : ZMod p)
  /-- Bind the second source register index to its witness column. -/
  rs2Index : w 6 = (input.rs2.toNat : ZMod p)
  /-- Bind the destination register index to its witness column. -/
  rdIndex : w 7 = (input.rd.toNat : ZMod p)
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w 0).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w 1).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.data.lo = (w 33).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.data.hi = (w 34).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w 13).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w 14).val

/-- Public initialization and ROM tables for this family. -/
abbrev RVAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  Trace.RVPooledHistoryInputs trace initial cells program

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .subwordMemory) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step computes the aligned cell and transfers the row's byte or halfword. It sets the final PC and changes no other visible state. -/
def rvSpec (input : RVInput) (output : Output) : Prop :=
  output.cell.toBitVec.toNat = (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 ∧
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' (if input.store then
        (input.before.store output.cell.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
      else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

end Airbender.SubwordMemory
