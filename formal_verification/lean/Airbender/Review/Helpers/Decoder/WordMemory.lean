import Airbender.Review.Helpers.Context.WordMemory
import Airbender.Review.Helpers.Decoder.Program

namespace Airbender.WordMemory
open Arithmetic Trace

/-- Native v2 LW/SW projection of the original Sail constructors. Retain x0
    loads, sign-extended immediates and funct3; only unused register indices clear. -/
def decoderFields : SailRV32.instruction → Option (DecoderData WordMemoryFamily)
  | .LOAD (imm, .Regidx rs1, .Regidx rd, false, 4) =>
    some ⟨.wordMemory, rs1, 0, rd,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 0, 2⟩
  | .STORE (imm, .Regidx rs2, .Regidx rs1, 4) =>
    some ⟨.wordMemory, rs1, rs2, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) imm), 1, 2⟩
  | _ => none

/-- Selected word-memory program followed by the complete native minus-one tail.
    Logical setup construction is separate from physical Rust generation/export. -/
structure DecoderSetup where
  program : List (ProgramEntry WordMemoryFamily)
  padding : Nat

def DecoderSetup.row {p : Nat} (setup : DecoderSetup)
    (i : Fin (setup.program.length + setup.padding)) : Vector (ZMod p) 10 :=
  if h : i.val < setup.program.length then (setup.program.get ⟨i.val, h⟩).query
  else Vector.replicate 10 (-1)

def DecoderSetup.table {p : Nat} [Fact p.Prime] (setup : DecoderSetup) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.V2WordMemoryDecoder"
  length := setup.program.length + setup.padding
  row := setup.row
  index query := setup.program.toArray.findIdx (fun entry => entry.query == query)
  Spec query := ∃ i, query = setup.row i
  contains_iff _ := Iff.rfl
}

/-- Actual public bytes and pure original Sail decoding at RV32 PCs 4*i.
    Missing/unsupported/effectful entries and insufficient capacity fail. -/
def decoderSetupImage (before : Reference.RiscV.Sail.State)
    (wordCount logCapacity : Nat) : Option DecoderSetup :=
  if wordCount ≤ 2 ^ logCapacity then do
    let program ← programImageWith decoderFields before
      ((List.range wordCount).map fun i => BitVec.ofNat 32 (4 * i))
    pure ⟨program, 2 ^ logCapacity - wordCount⟩
  else none

/-- Complete padded logical membership over the imported ten-column query. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p WordMemoryFamily)
    (setup : DecoderSetup) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.WordMemory
