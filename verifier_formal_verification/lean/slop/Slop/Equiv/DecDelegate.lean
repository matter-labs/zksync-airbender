import Slop.Equiv.Close

/-! Sail's decoder on our table's delegation rows (CSR 0x7c7, source and `rd` 0, `RV.decodeCsr`): Sail's
`CSRReg` on CSR 0x7c7. Written by hand. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem dec_delegate_rw (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rw)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_rs (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 2) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rs)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_rc (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 3) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .rc)) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
