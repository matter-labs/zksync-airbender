module
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Core.BabyBearPrime
public import Slop.Trace.RVHistory

@[expose] public section

/-! Boot seeds from the inits/teardowns circuits, for any trace model: the register seeds followed by the `Init` tokens
    of instances whose top bits pass the verifier's check are the zero boot image of the registers and their windows
    (`boot_seed_image`), and a state whose tracked cells read as that image reads 0 in every tracked cell
    (`rv_image_zero`). -/

namespace Airbender.Trace.Proofs
open Arithmetic

theorem initialToken_injective {p : Nat} {cell : Cell} {a b : BitVec 32}
    (same : cell.initialToken (p := p) a = cell.initialToken b) : a = b := by
  have pair := (Nat.pair_eq_pair.mp (congrArg MemoryToken.value same))
  have word : Word.ofBitVec a = Word.ofBitVec b := by
    cases ha : Word.ofBitVec a
    cases hb : Word.ofBitVec b
    simp only [ha, hb] at pair
    rw [pair.1, pair.2]
  rw [← Word.ofBitVec_roundtrip a, word, Word.ofBitVec_roundtrip]

/-- A state whose tracked cells read as the zero boot image reads 0 in every tracked cell. -/
theorem rv_image_zero {p : Nat} {s : RV.State} {cells : List Cell}
    (image : initialImageRV (p := p) s cells = some (ROMView.nativeBootImage cells)) :
    ∀ cell ∈ cells, cell.readRV s = some 0 := by
  have reads := rvImage_reads cells _ image
  clear image
  induction cells with
  | nil => simp
  | cons cell rest ih =>
    rcases List.forall₂_cons.mp reads with ⟨⟨value, read, same⟩, tail⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [read, initialToken_injective same.symm]
    · exact ih tail other member

/-- The register seeds, then the `Init` tokens of instances with checked top bits, are the zero boot image of the
    registers, then the instances' windows. -/
theorem boot_seed_image {layout : InitsTeardowns.Layout} (claims : InitsTeardowns.Claims layout)
    {seeds : List (MemoryToken babyBearModulus)} {cells : List Cell}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (topBits : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList))
    (seedsEq : seeds = registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens)
    (domain : cells = registerCells ++
      InitsTeardowns.windowCells layout (inits.flatMap fun w => w.topBits.toList)) :
    seeds = ROMView.nativeBootImage cells := by
  rw [seedsEq, domain, (claims.bootImage inits topBits).2]
  simp only [registerSeeds, ROMView.nativeBootImage, List.map_append]

end Airbender.Trace.Proofs
