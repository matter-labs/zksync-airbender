import Slop.Equiv.Close
import Slop.RV.DecodeCsr

/-! Sail's decoder on our table's delegation rows (`csrrw x0, <csr>, x0`, `RV.decodeCsr`): Sail's `CSRReg` on that
CSR, for any CSR (`dec_csrrw00`), hence for any decoded kind (`dec_delegate`). Written by hand. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

/-- `csrrw x0, c, x0`, any `c`. -/
theorem dec_csrrw00 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) (c : BitVec 12) (h4 : Bits w 20 12 c.toNat) :
    runSail (ext_decode w) σ = .ok (Airbender.csrToSail c 0 0) σ := by
  walk_decoder hs
  rw [Slop.runF_pure]
  subst_known
  bits_lsb
  simp only [Airbender.csrToSail, EStateM.Result.ok.injEq, instruction.CSRReg.injEq, Prod.mk.injEq, and_true,
    true_and]
  and_intros
  · apply BitVec.eq_of_getElem_eq; intro i hi
    rename_i hb
    simp only [Sail.BitVec.extractLsb, BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem]
    have := hb (20 + i) (by omega) (by omega)
    simp only [Nat.add_sub_cancel_left] at this
    rw [show c[i] = c.toNat.testBit i from BitVec.getElem_eq_testBit_toNat c i hi, ← this]
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb]; simp [Nat.add_comm]; omega
  all_goals first | rfl | decide | (congr 1; close_field) | close_field
/-- A delegation call of any kind the CSR table gives. -/
theorem dec_delegate (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 1) (h2 : Bits w 15 5 0) (h3 : Bits w 7 5 0) {k : RV.DelegationKind}
    (hk : RV.DelegationKind.ofCsr (w.extractLsb' 20 12) = some k) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.delegate k)) σ := by
  rw [show Airbender.toSail (.delegate k) = Airbender.csrToSail k.csr 0 0 from rfl, RV.ofCsr_csr hk]
  exact dec_csrrw00 w σ hs h0 h1 h2 h3 _ (by unfold Bits; rw [BitVec.extractLsb'_toNat])

end Slop.Equiv
