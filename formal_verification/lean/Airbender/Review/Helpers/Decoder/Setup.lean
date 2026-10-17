import Airbender.Review.Helpers.Decoder.Program

namespace Airbender.Trace

/-- Selected-profile decoder rows followed by the native all-minus-one tail.
    This is the logical v2 setup view; Rust generation/export fidelity and lookup
    authentication are separate. No table equivalence is an interface premise. -/
structure DecoderSetup where
  program : List ProgramEntry
  padding : Nat

/-- Retain every committed tail row rather than filtering it out of membership. -/
def DecoderSetup.row {p : Nat} (setup : DecoderSetup)
    (i : Fin (setup.program.length + setup.padding)) : Vector (ZMod p) 10 :=
  if h : i.val < setup.program.length then (setup.program.get ⟨i.val, h⟩).query
  else Vector.replicate 10 (-1)

def DecoderSetup.table {p : Nat} [Fact p.Prime] (setup : DecoderSetup) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.V2Decoder"
  length := setup.program.length + setup.padding
  row := setup.row
  index query := setup.program.toArray.findIdx (fun entry => entry.query == query)
  Spec query := ∃ i, query = setup.row i
  contains_iff _ := Iff.rfl
}

/-- Construct the selected-profile setup from actual public byte reads and pure
    original Sail decoding at native PCs 4*i. Missing/unsupported/effectful entries
    fail. Capacity is a power of two; PCs retain native RV32 truncation. -/
def decoderSetupImage (before : Reference.RiscV.Sail.State)
    (wordCount logCapacity : Nat) : Option DecoderSetup :=
  if wordCount ≤ 2 ^ logCapacity then do
    let program ← programImage before ((List.range wordCount).map fun i => BitVec.ofNat 32 (4 * i))
    pure ⟨program, 2 ^ logCapacity - wordCount⟩
  else none

/-- Logical native lookup membership over the complete padded setup. Equations
    rule out padding; public construction supplies actual Sail source evidence.
    Cryptographic enforcement of membership remains a separate boundary. -/
def Decoded {p : Nat} [Fact p.Prime] (trace : Data p) (setup : DecoderSetup) : Prop :=
  ∀ row ∈ trace.rows, setup.table.Contains #[] row.decoderQuery

end Airbender.Trace
