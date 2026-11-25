module
public import Human.Circuits.UnifiedReduced.Proth120Windows

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open InitsTeardowns Trace Arithmetic

theorem window_tokens : WindowTokensClaim := by
  intro w s r topBound
  let top := w.topBits[s]
  have ht : top < 256 := topBound
  have hr : r.val < 2097152 := r.isLt
  change _ < 2 ^ 31 ∧ _ ∧ _ ∧ _
  let addr := top * 8388608 + r.val * 4
  have below : addr < 2 ^ 31 := by dsimp [addr]; omega
  have aligned : addr % 4 = 0 := by dsimp [addr]; omega
  have low : r.val * 4 % 65536 = addr % 65536 := by dsimp [addr]; omega
  have high : r.val / 16384 + top * 128 = addr / 65536 := by dsimp [addr]; omega
  have shift : top * 128 % 4294967296 = top * 128 := Nat.mod_eq_of_lt (by omega)
  have image : addressCode (p := proth120Modulus) importedLayout top r =
      (Cell.ram (BitVec.ofNat 32 addr)).addressCode := by
    have loBound : r.val * 4 % 65536 < proth120Modulus :=
      lt_trans (Nat.mod_lt _ (by decide : 0 < 65536)) (by decide)
    have hiBound : r.val / 16384 + top * 128 < proth120Modulus := by
      rw [high]; exact lt_of_lt_of_le (Nat.div_lt_of_lt_mul (by omega : addr < 65536 * 65536)) (by decide)
    simp only [addressCode, addressLimbs, setupLow, setupHigh, topShift,
      show importedLayout.wordBits = 2 by rfl, show importedLayout.traceLog = 21 by rfl,
      Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.shiftLeft_eq, shift, ← Nat.cast_add, Cell.addressCode,
      Word.ofBitVec, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt (show addr < 4294967296 by omega), limbBase]
    rw [ZMod.val_natCast_of_lt loBound, ZMod.val_natCast_of_lt hiBound, low, high]
  refine ⟨below, ?_, ?_, ?_⟩
  · change (BitVec.ofNat 32 addr).toNat % 4 = 0
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show addr < 2 ^ 32 by omega)] using aligned
  · change initToken (p := proth120Modulus) importedLayout top r = (Cell.ram (BitVec.ofNat 32 addr)).initialToken 0
    simp only [initToken, Cell.initialToken, image]
    rfl
  · exact congrArg (fun a => MemoryToken.mk a _ _) image

theorem window_tokens_satisfiable : WindowTokensSatisfiableClaim :=
  ⟨⟨#v[0, 255], fun _ _ => 0⟩, ⟨1, by decide⟩, ⟨2097151, by decide⟩, by decide, rfl, rfl⟩

end Airbender.UnifiedReduced.Proth120
