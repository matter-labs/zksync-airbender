import Airbender.Data.Setup.Keccak.ThetaRhoGeneric
import Airbender.Data.Setup.Keccak.Chi5Generic

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
-- The proofs unfold only the short tag columns of the complete native tables.
set_option maxHeartbeats 500000

private theorem theta_rho_tag_column : thetaRhoGeneric.columns[8] =
    ⟨#[.affine 65536 4 0, .affine 524288 58 0, .affine 121 59 0,
      .affine 121 60 0, .affine 3604238 0 0]⟩ := by rfl

private theorem chi5_tag_column : chi5Generic.columns[10] =
    ⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ := by rfl

/-- The actual field tag selects the theta/rho controller region. -/
theorem theta_rho_controller_field_tag_region (i : Fin thetaRhoGeneric.length)
    (tag : ((thetaRhoGeneric.row i).map (fun value : Int => (value : ZMod babyBearModulus)))[8] = 59) :
    589824 ≤ i.val ∧ i.val < 589945 := by
  simp only [TableData.row, Vector.getElem_map] at tag
  change (signedValue ((thetaRhoGeneric.columns[8].get? (0 + i.val)).getD 0) : ZMod babyBearModulus) = 59 at tag
  rw [Nat.zero_add] at tag
  rw [theta_rho_tag_column] at tag
  simp only [Column.get?, getFromBlocks, Block.get?, Block.length] at tag
  split_ifs at tag
  all_goals try simp only [zero_mul, add_zero] at tag
  all_goals first
    | omega
    | (have values := congrArg ZMod.val tag
       simp only [Option.getD_some, Option.getD_none, Int.toNat_natCast,
         signedValue_cast] at values
       first
       | change 4 = 59 at values; omega
       | change 58 = 59 at values; omega
       | change 60 = 59 at values; omega
       | change 0 = 59 at values; omega)

/-- The actual field tag selects the chi5 controller region. -/
theorem chi5_controller_field_tag_region (i : Fin chi5Generic.length)
    (tag : ((chi5Generic.row i).map (fun value : Int => (value : ZMod babyBearModulus)))[10] = 66) :
    1048576 ≤ i.val ∧ i.val < 1048697 := by
  simp only [TableData.row, Vector.getElem_map] at tag
  change (signedValue ((chi5Generic.columns[10].get? (0 + i.val)).getD 0) : ZMod babyBearModulus) = 66 at tag
  rw [Nat.zero_add] at tag
  rw [chi5_tag_column] at tag
  simp only [Column.get?, getFromBlocks, Block.get?, Block.length] at tag
  split_ifs at tag
  all_goals try simp only [zero_mul, add_zero] at tag
  all_goals first
    | omega
    | (have values := congrArg ZMod.val tag
       simp only [Option.getD_some, Option.getD_none, Int.toNat_natCast,
         signedValue_cast] at values
       first
       | change 65 = 66 at values; omega
       | change 0 = 66 at values; omega)

end Airbender.Keccak.Split.Native.Fixed.Proofs
