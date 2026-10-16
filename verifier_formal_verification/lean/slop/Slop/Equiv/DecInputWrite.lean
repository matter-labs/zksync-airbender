import Slop.Equiv.Close

/-! Sail's decoder on our table's CSR 0x7c0 rows (`RV.decodeCsr`), write (`rd = x0`), csrrw, csrrs, csrrc: Sail's `CSRReg` on CSR
0x7c0. Written by hand (the rows have side conditions, which `gen/decode_rows.py` does not generate). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem dec_write_rw (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 7 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputWrite .rw (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  close_row

theorem dec_write_rs (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 2) (h2 : Bits w 7 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputWrite .rs (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  close_row

theorem dec_write_rc (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 3) (h2 : Bits w 7 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputWrite .rc (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
