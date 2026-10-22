import Slop.Equiv.DecMopR

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

/-! `mop.r.N` rows (2 of 3): see `DecMopR.lean`. -/

/-- `mop.r.N`, N = 16 … 19. -/
theorem dec_mopr_4 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 48) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 20 … 23. -/
theorem dec_mopr_5 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 49) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 24 … 27. -/
theorem dec_mopr_6 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 50) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 28. -/
theorem dec_mopr_7_0 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 51) (h3 : Bits w 20 2 0) (h4 : Bits w 22 4 7)
    (h5 : Bits w 7 5 0) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

end Slop.Equiv
