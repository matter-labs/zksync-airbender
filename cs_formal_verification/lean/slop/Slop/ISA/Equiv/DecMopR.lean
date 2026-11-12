import Slop.ISA.Equiv.DecSys4

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

/-! Sail's decoder on our `mop.r.N` rows (`RV.decodeMopR`), for any `rd`, split by the bits of `N` (Sail has an
instruction at `N = 28`, a Zicfiss one, that the walk excludes only with all of `N` and `rd = x0` known; `N` = 28 …
31 decode only with `rd = x0`). Written by hand. The clauses before the `mop` ones: `dec_sys4`, walked once. -/

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
    | (apply BitVec.eq_of_toNat_eq   -- `rd = x0` known (N = 28 … 31): Sail's field is the literal 0
       simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, Functions.regidx_bit_width,
         Nat.shiftRight_eq_div_pow]
       unfold Bits at *
       simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow] at *
       omega)
    | (apply BitVec.eq_of_getLsbD_eq; intro j hj
       try simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, Functions.regidx_bit_width] at hj ⊢
       have hj5 : j < 5 := by simpa using hj
       interval_cases j <;> simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero] <;> simp_all [-BitVec.getLsbD_eq_getElem])))

/-- `mop.r.N`, N = 0 … 3. -/
theorem dec_mopr_0 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 32) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 4 … 7. -/
theorem dec_mopr_1 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 33) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 8 … 11. -/
theorem dec_mopr_2 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 34) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 12 … 15. -/
theorem dec_mopr_3 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 35) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 16 … 19. -/
theorem dec_mopr_4 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 48) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 20 … 23. -/
theorem dec_mopr_5 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 49) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 24 … 27. -/
theorem dec_mopr_6 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 50) (h4 : Bits w 22 4 7) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

/-- `mop.r.N`, N = 28 … 31 (bits 20–21 are part of the operands, not of the case). -/
theorem dec_mopr_7 (w : BitVec 32) (σ : SailState) (hs : Airbender.Configured σ) (h0 : Bits w 0 7 115)
    (h1 : Bits w 12 3 4) (h2 : Bits w 26 6 51) (h4 : Bits w 22 4 7) (h5 : Bits w 7 5 0) :
    runSail (ext_decode w) σ = .ok (Airbender.toSail (.xorRot (w.extractLsb' 30 1 ++ w.extractLsb' 26 2 ++
      w.extractLsb' 20 2) (w.extractLsb' 7 5) (w.extractLsb' 15 5))) σ := by
  refine (dec_sys4 w σ hs h0 h1).trans ?_
  walk_decoder hs
  mopr_row

end Slop.Equiv
