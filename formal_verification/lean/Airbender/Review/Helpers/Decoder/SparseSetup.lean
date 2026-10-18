import Airbender.Review.Helpers.Decoder.Program

namespace Airbender.Trace

/-- Read every public word. Unsupported pure decoder results become holes;
    missing bytes or effectful decoding reject the constructor. -/
def programSlotWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option (Option (ProgramEntry Kind)) := do
  let bits ← match (Cell.ram pc).read before with
    | .ok bits _ => some bits
    | .error _ _ => none
  let instruction ← match SailRV32.Functions.encdec_backwards bits with
    | .pure instruction => some instruction
    | .impure _ _ => none
  pure ((projection instruction).map fun data => ⟨pc, bits, instruction, data⟩)

/-- Native indexed decoder slots, including unsupported words and the full tail. -/
structure SparseDecoderSetup (Kind : Type) where
  slots : List (Option (ProgramEntry Kind))
  padding : Nat

def SparseDecoderSetup.program (setup : SparseDecoderSetup Kind) : List (ProgramEntry Kind) :=
  setup.slots.filterMap id

def SparseDecoderSetup.row {p : Nat} (setup : SparseDecoderSetup Kind)
    (i : Fin (setup.slots.length + setup.padding)) : Vector (ZMod p) 10 :=
  match (setup.slots[i.val]?).bind id with
  | some entry => entry.query
  | none => Vector.replicate 10 (-1)

def SparseDecoderSetup.table {p : Nat} [Fact p.Prime] (setup : SparseDecoderSetup Kind) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.V2SparseDecoder"
  length := setup.slots.length + setup.padding
  row := setup.row
  index query := setup.slots.toArray.findIdx fun slot =>
    match slot with
    | some entry => entry.query == query
    | none => Vector.replicate 10 (-1) == query
  Spec query := ∃ i, query = setup.row i
  contains_iff _ := Iff.rfl
}

/-- Native PCs remain 4*i across holes; supported words are never compacted. -/
def sparseDecoderSetupImageWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (count logCapacity : Nat) :
    Option (SparseDecoderSetup Kind) :=
  if count ≤ 2 ^ logCapacity then do
    let slots ← ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)).mapM
      (programSlotWith projection before)
    pure ⟨slots, 2 ^ logCapacity - count⟩
  else none

end Airbender.Trace
