module
public import Human.Circuits.WordMemory.Artifact
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
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
  store : Bool
  source : Word
  immediate : Word
  readData : Word
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  rd : RV.Reg
  encodedImmediate : BitVec 12
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding): LW is
    `.load 4 true` (sign extension of a full word is the identity). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  if input.store then .store 4 input.rs2 input.rs1 (input.encodedImmediate.signExtend 32)
  else .load 4 true input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Output) (w : Nat → ZMod p) : Prop where
  sourceLo : input.source.lo = (w Variables.sourceLo).val
  sourceHi : input.source.hi = (w Variables.sourceHi).val
  immediateLo : input.immediate.lo = (w Variables.immediateLo).val
  immediateHi : input.immediate.hi = (w Variables.immediateHi).val
  readLo : input.readData.lo = (w readDataLo).val
  readHi : input.readData.hi = (w readDataHi).val
  addressLo : output.address.lo = (w (if input.store then writeAddressLo else readAddressLo)).val
  addressHi : output.address.hi = (w (if input.store then writeAddressHi else readAddressHi)).val
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  outputLo : output.data.lo = (w writeDataLo).val
  outputHi : output.data.hi = (w writeDataHi).val
  finalPCLo : output.pc.lo = (w Variables.finalPCLo).val
  finalPCHi : output.pc.hi = (w Variables.finalPCHi).val

/-- Trace mapping in RV32 terms: the row's pre-state is the RV state at its clock position, and its
    decoder entry in the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Name the operands, address, transferred data and PCs using the imported variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.wordMemory, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .wordMemory ∧ (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- LW/SW's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- Assumptions of the RV statements: public initialization and modeled tables. -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVPooledHistoryInputs trace initial cells program

end Airbender.WordMemory
