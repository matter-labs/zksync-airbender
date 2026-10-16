import Slop.Equiv.Close

/-! Sail's decoder on our table's delegation rows (`csrrw x0, <csr>, x0`, `RV.decodeCsr`): Sail's `CSRReg` on that
CSR. Written by hand. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem dec_delegate_blakeRound (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1991) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .blakeRound)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_blakeG (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1992) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .blakeG)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_bigint (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1994) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .bigint)) σ := by
  walk_decoder hs
  close_row

theorem dec_delegate_keccak (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (h4 : Bits w 20 12 1995) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate .keccak)) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
