import Slop.Equiv.Close

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

/-! Sail's decoder on our `mop.r.N` rows (`RV.decodeMopR`), for any `rd`, split by the bits of `N` (Sail has an
instruction at `N = 28`, a Zicfiss one, that the walk excludes only with all of `N` and `rd = x0` known; `N` = 28 …
31 decode only with `rd = x0`). Written by hand. -/

/-- The bits of `N` as Sail's decoder takes them = as `RV.decodeMopR` does. -/
theorem mopR_n (w : BitVec 32) :
    Sail.BitVec.extractLsb w 30 30 ++ (Sail.BitVec.extractLsb w 27 26 ++ Sail.BitVec.extractLsb w 21 20) =
      w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++ w.extractLsb' 20 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb] at *
  interval_cases i <;> simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb'] <;> simp

/-- After `walk_decoder` on a `mop.r.N` row: `N` by `mopR_n`, the registers field by field. -/
macro "mopr_row" : tactic => `(tactic| (
  rw [Slop.runF_pure]
  bits_lsb
  simp only [Airbender.toSail, EStateM.Result.ok.injEq, instruction.ZIMOP_MOP_R.injEq, Prod.mk.injEq, and_true]
  refine ⟨mopR_n _, ?_, ?_⟩ <;> congr 1 <;> first
    | close_field
    | (apply BitVec.eq_of_getLsbD_eq; intro j hj
       try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width] at hj ⊢
       have hj5 : j < 5 := by simpa using hj
       interval_cases j <;> simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero] <;> simp_all [-BitVec.getLsbD_eq_getElem])))

end Slop.Equiv
