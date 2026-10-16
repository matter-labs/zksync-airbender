import Slop.Equiv.Close

/-! Sail's decoder on our table's CSR 0x7c0 rows (`RV.decodeCsr`), read (source 0), csrrw, csrrs, csrrc: Sail's `CSRReg` on CSR
0x7c0. Written by hand (the rows have side conditions, which `gen/decode_rows.py` does not generate). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem dec_read_rw (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputRead .rw (w.extractLsb' 7 5))) σ := by
  walk_decoder hs
  close_row

theorem dec_read_rs (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 2) (h2 : Bits w 15 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputRead .rs (w.extractLsb' 7 5))) σ := by
  walk_decoder hs
  close_row

theorem dec_read_rc (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 3) (h2 : Bits w 15 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputRead .rc (w.extractLsb' 7 5))) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
