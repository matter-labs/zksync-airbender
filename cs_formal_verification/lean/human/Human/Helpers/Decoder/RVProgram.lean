import Human.Helpers.Decoder.Program
import Human.ISA.RV32
import Human.ISA.Sail.Airbender

/-! RV sibling of the public program table (`Trace.programEntryWith`): the instruction is `RV.decode` of the public
bytes, viewed in Sail's vocabulary (`Airbender.toSail`). Kept in its own module so that importing `Airbender` does not
shadow names in `Trace` users. -/

noncomputable section

namespace Airbender.Trace
open Arithmetic

/-- RV sibling of `programEntryWith`: the public encoding is read from our spec's byte memory (`RV.read`), the
    instruction is `RV.decode` of it viewed in Sail's vocabulary (`toSail`); no Sail state or decoder call. The fetch
    guard is the ROM bound and alignment of `RV.ROM_END` (equal to `ROM.limit`). -/
noncomputable abbrev rvProgramEntryWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : RV.State) (pc : BitVec 32) :
    Option (ProgramEntry Kind) := do
  if ¬(pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) then none else
  let bits := RV.read before.mem pc 4
  let i ← RV.decode bits
  let instruction := Airbender.toSail i
  let data ← projection instruction
  pure ⟨pc, bits, instruction, data⟩

/-- RV sibling of `programImageWith`. -/
noncomputable abbrev rvProgramImageWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (before : RV.State) (addresses : List (BitVec 32)) :
    Option (List (ProgramEntry Kind)) := addresses.mapM (rvProgramEntryWith projection before)

noncomputable abbrev rvProgramEntry := rvProgramEntryWith decoderFields
noncomputable abbrev rvProgramImage := rvProgramImageWith decoderFields

end Airbender.Trace
