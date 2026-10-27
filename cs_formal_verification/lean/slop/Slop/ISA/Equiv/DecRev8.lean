import Slop.ISA.Equiv.Close

/-! Sail's decoder on our `rev8` row (Zbb/Zbkb; our config has Zbkb). Written by hand. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

/-- Two adjacent fields as one. -/
theorem bits_join {w : BitVec 32} {a b : Nat} (ha : Bits w 25 7 a) (hb : Bits w 20 5 b) : Bits w 20 12 (a * 32 + b) := by
  unfold Bits at *
  simp only [Nat.shiftRight_eq_div_pow] at *
  omega

theorem dec_rev8_12 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 19)
    (h1 : Bits w 12 3 5) (h2 : Bits w 20 12 0x698) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.rev8 (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  close_row

/-- `rev8` as our table states it: funct7 = 0x34 and rs2 = 24 (funct12 = 0x698). -/
theorem dec_rev8 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 19) (h1 : Bits w 12 3 5)
    (h2 : Bits w 25 7 52) (h3 : Bits w 20 5 24) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.rev8 (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ :=
  dec_rev8_12 w σ hs h0 h1 (bits_join h2 h3)

end Slop.Equiv
