import Slop.Equiv.Close

/-! Sail's decoder on our table's delegation rows (CSR 0x7c7, source and `rd` 0, `RV.decodeCsr`): Sail's
`CSRImm` on CSR 0x7c7. Written by hand. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem dec_delegate_rwi (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 5) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rwi)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_rsi (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 6) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rsi)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_rci (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 7) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rci)) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
