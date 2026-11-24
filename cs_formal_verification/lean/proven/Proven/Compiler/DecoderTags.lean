module
public import Proven.Compiler.DecoderRows

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic Metadata Verification
set_option warningAsError true
set_option maxRecDepth 65536

private theorem cast_not_46 (value : Nat) (bounded : value < babyBearModulus)
    (different : value ≠ 46) : (value : F) ≠ 46 := by
  intro equal
  have natEqual := congrArg ZMod.val equal
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt bounded,
    show (46 : F).val = 46 from by kernel_rfl] at natEqual
  exact different natEqual

private theorem shift_tag (index : Fin 524545) :
    (shiftBinopRow index)[9] < 10 := by
  unfold shiftBinopRow binaryByteRow
  dsimp only
  split_ifs <;> norm_num [babyBearModulus]

private theorem unified_tag (words : Nat → BitVec 32) (index : Fin 2097537) :
    (UnifiedReduced.Setup.rowWith words index)[9] < babyBearModulus ∧
    (UnifiedReduced.Setup.rowWith words index)[9] ≠ 46 := by
  have bound := index.isLt
  unfold babyBearModulus
  unfold UnifiedReduced.Setup.rowWith
  split
  · unfold UnifiedReduced.Setup.fixedRow
    dsimp only
    split
    · rename_i h
      simp only [UnifiedReduced.Setup.binaryRow, Vector.getElem_set_self]
      have small := shift_tag (⟨index.val, h⟩ : Fin 524545)
      unfold UnifiedReduced.Setup.binaryTag
      split_ifs <;> omega
    · split
      · change 1 < 2013265921 ∧ (1 : Nat) ≠ 46
        decide
      · split
        · change 5 < 2013265921 ∧ (5 : Nat) ≠ 46
          decide
        · split
          · change 2 < 2013265921 ∧ (2 : Nat) ≠ 46
            decide
          · split
            · change 51 < 2013265921 ∧ (51 : Nat) ≠ 46
              decide
            · change 47 + (index.val - 786817) / 65536 < 2013265921 ∧
                47 + (index.val - 786817) / 65536 ≠ 46
              omega
  · norm_num

/-- Every fixed native discriminator differs from the decoder discriminator. -/
theorem fixed_not_decoder (family : RVMachineDecoderFamily) (isTagged : tagged family = true)
    (words : Nat → BitVec 32) (index : Nat) :
    ((fixedRow family words index)[width family - 1]?).getD 0 ≠ 46 := by
  simp only [fixedRow]
  cases family with
  | pooled family =>
    cases family with
    | addSub => simp [tagged] at isTagged
    | jumpBranchSlt =>
      simp [width, hasFunct3]
      change (((NativeFixedRows.jumpBranch (Fin.ofNat 4456448 index))[9] : Nat) : F) ≠ 46
      apply cast_not_46
      · unfold NativeFixedRows.jumpBranch
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
      · unfold NativeFixedRows.jumpBranch
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
    | mulDiv =>
      simp [width, hasFunct3]
      change (((NativeFixedRows.mulDiv (Fin.ofNat 270336 index))[8] : Nat) : F) ≠ 46
      apply cast_not_46
      · unfold NativeFixedRows.mulDiv
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
      · unfold NativeFixedRows.mulDiv
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
    | shiftBinop =>
      simp [width, hasFunct3]
      change (((shiftBinopRow (Fin.ofNat 524545 index))[9] : Nat) : F) ≠ 46
      apply cast_not_46 <;> have small := shift_tag (Fin.ofNat 524545 index)
      · unfold babyBearModulus; omega
      · omega
    | wordMemory =>
      simp [width, hasFunct3]
      change (((NativeFixedRows.wordMemory words (Fin.ofNat 1048577 index))[8] : Nat) : F) ≠ 46
      apply cast_not_46
      · unfold NativeFixedRows.wordMemory
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
      · unfold NativeFixedRows.wordMemory
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
    | subwordMemory =>
      simp [width, hasFunct3]
      change (((subwordRow words (Fin.ofNat 13238273 index))[8] : Nat) : F) ≠ 46
      apply cast_not_46
      · unfold subwordRow subwordDataRow
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
      · unfold subwordRow subwordDataRow
        dsimp only
        split_ifs <;> norm_num [babyBearModulus]
  | unified =>
    simp [width, hasFunct3]
    change (((NativeFixedRows.unified words (Fin.ofNat 2097537 index))[9] : Nat) : F) ≠ 46
    exact cast_not_46 _ (unified_tag words _).1 (unified_tag words _).2

end Airbender.Compiler.NativePublicSetup.Proofs
