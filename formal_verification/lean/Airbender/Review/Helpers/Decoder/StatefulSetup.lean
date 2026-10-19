import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.Trace

/-- Stateful decoding uses the original Sail interpreter on the public state.
    Unlike the pure constructor, this permits configuration reads such as
    `misa.M`. Its source theorem retains the actual decoder execution. -/
abbrev programEntryRunWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option (ProgramEntry Kind) := do
  let bits ← match (Cell.ram pc).read before with
    | .ok bits _ => some bits
    | .error _ _ => none
  let instruction ← match Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before with
    | .ok instruction _ => some instruction
    | .error _ _ => none
  let data ← projection instruction
  pure ⟨pc, bits, instruction, data⟩

/-- Construct entries for public `addresses` by running Sail decoding in
    `before`, including configuration reads. Failure at any address rejects the
    whole image. The addresses and starting state are independent of the witness. -/
abbrev programImageRunWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) :
    Option (List (ProgramEntry Kind)) := addresses.mapM (programEntryRunWith projection before)

/-- Read every public word and run original Sail decoding in the supplied public
    state. Unsupported instructions become holes; byte/decoder errors reject. -/
def programSlotRunWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (pc : BitVec 32) :
    Option (Option (ProgramEntry Kind)) := do
  let bits ← match (Cell.ram pc).read before with
    | .ok bits _ => some bits
    | .error _ _ => none
  let instruction ← match Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) before with
    | .ok instruction _ => some instruction
    | .error _ _ => none
  pure ((projection instruction).map fun data => ⟨pc, bits, instruction, data⟩)

/-- Stateful sparse decoding retains native PCs, holes and the complete tail. -/
def sparseDecoderSetupImageRunWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : Reference.RiscV.Sail.State) (count logCapacity : Nat) :
    Option (SparseDecoderSetup Kind) :=
  if count ≤ 2 ^ logCapacity then do
    let slots ← ((List.range count).map fun i => BitVec.ofNat 32 (4 * i)).mapM
      (programSlotRunWith projection before)
    pure ⟨slots, 2 ^ logCapacity - count⟩
  else none

end Airbender.Trace
