import Slop.ISA.Equiv.Close

/-! Sail's decoder on words with opcode SYSTEM and `funct3 = 4` (our `mop` rows, `DecMop`, `DecMopR`): the
~400 clauses these bits alone rule out, skipped once for all rows. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

/-- Sail's decoder on a SYSTEM word with `funct3 = 4`, from the first clause these bits do not decide. -/
noncomputable def decodeSys4 (w : BitVec 32) : SailM instruction := decoder_rest% w ⟨0, 7, 115⟩ ⟨12, 3, 4⟩

theorem dec_sys4 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) : runSail (ext_decode w) σ = runSail (decodeSys4 w) σ := by
  walk_decoder_rest hs

end Slop.Equiv
