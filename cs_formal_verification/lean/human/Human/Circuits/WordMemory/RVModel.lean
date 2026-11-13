module
public import Human.Circuits.WordMemory.Artifact
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Context.RVRowModel
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.ISA.RV32

@[expose] public section

/-! RV32 vocabulary for the LW/SW circuit (RV registers, an `RV.State` pre-state and the
    instruction `RV.decode` of the public program entry). `Output` is the effective address, transferred word and next
    PC. There is no MMIO and no configuration in the RV memory map, so no memory-map or configuration premise is
    needed. -/

namespace Airbender.WordMemory
open Arithmetic Trace Variables

/-- The circuit's input in RV32 terms: operation (SW when `store`), operand words, start PC, register indices, the
    original 12-bit immediate and the row's pre-state. `readData` is the read-port word: RAM on LW, rs2 on SW, and
    an unused placeholder on ROM loads. -/
structure RVInput where
  /-- Select a store when true and a load when false. -/
  store : Bool
  /-- The address-base operand word. -/
  source : Word
  /-- The decoded immediate word. -/
  immediate : Word
  /-- The word read by the circuit port. -/
  readData : Word
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

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding): LW is
    `.load 4 true` (sign extension of a full word is the identity). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  if input.store then .store 4 input.rs2 input.rs1 (input.encodedImmediate.signExtend 32)
  else .load 4 true input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the address-base operand to its witness column. -/
  sourceLo : input.source.lo = (w Variables.sourceLo).val
  /-- Bind the high limb of the address-base operand to its witness column. -/
  sourceHi : input.source.hi = (w Variables.sourceHi).val
  /-- Bind the low limb of the decoded immediate to its witness column. -/
  immediateLo : input.immediate.lo = (w Variables.immediateLo).val
  /-- Bind the high limb of the decoded immediate to its witness column. -/
  immediateHi : input.immediate.hi = (w Variables.immediateHi).val
  /-- Bind the low limb of the read-port word to its witness column. -/
  readLo : input.readData.lo = (w readDataLo).val
  /-- Bind the high limb of the read-port word to its witness column. -/
  readHi : input.readData.hi = (w readDataHi).val
  /-- Bind the low limb of the effective address to its witness column. -/
  addressLo : output.address.lo = (w (if input.store then writeAddressLo else readAddressLo)).val
  /-- Bind the high limb of the effective address to its witness column. -/
  addressHi : output.address.hi = (w (if input.store then writeAddressHi else readAddressHi)).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  /-- Bind the second source register index to its witness column. -/
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)
  /-- Bind the destination register index to its witness column. -/
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w initialPCLo).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w initialPCHi).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.data.lo = (w writeDataLo).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.data.hi = (w writeDataHi).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w Variables.finalPCLo).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w Variables.finalPCHi).val

/-- Public initialization and ROM tables for this family. -/
abbrev RVAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  Trace.RVPooledHistoryInputs trace initial cells program

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .wordMemory) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step computes the effective address and transfers the row's word. It sets the final PC and changes no other visible state. -/
def rvSpec (input : RVInput) (output : Output) : Prop :=
  output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec ∧
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' (if input.store then
        (input.before.store output.address.toBitVec output.data.toBitVec 4).setPC output.pc.toBitVec
      else (input.before.setReg input.rd output.data.toBitVec).setPC output.pc.toBitVec)

end Airbender.WordMemory
