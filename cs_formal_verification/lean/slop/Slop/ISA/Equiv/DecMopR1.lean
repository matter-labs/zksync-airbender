import Slop.ISA.Equiv.DecMopR

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

/-! `mop.r.N` rows (1 of 3): see `DecMopR.lean`. -/

/-- `mop.r.N`, N = 0 … 3. -/
theorem dec_mopr_0 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 32) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 4 … 7. -/
theorem dec_mopr_1 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 33) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 8 … 11. -/
theorem dec_mopr_2 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 34) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 12 … 15. -/
theorem dec_mopr_3 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 35) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  mopr_row

end Slop.Equiv
