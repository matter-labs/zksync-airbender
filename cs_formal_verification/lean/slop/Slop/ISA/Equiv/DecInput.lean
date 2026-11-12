import Slop.ISA.Equiv.Close

/-! Sail's decoder on our table's CSR rows (`RV.decodeCsr`): `csrrw rd, 0x7c0, x0`, `csrrw x0, 0x7c0, rs1` and the
delegation calls `csrrw x0, <csr>, x0` are Sail's `CSRReg (…, CSRRW)`. Written by hand (the rows have side
conditions, which `gen/decode_rows.py` does not generate). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

theorem dec_read (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputRead (w.extractLsb' 7 5))) σ := by
  walk_decoder hs
  close_row

theorem dec_write (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 7 5 0) (h3 : Bits w 20 12 1984) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.inputWrite (w.extractLsb' 15 5))) σ := by
  walk_decoder hs
  close_row

end Slop.Equiv
