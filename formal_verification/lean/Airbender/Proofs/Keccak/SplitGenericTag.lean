import Airbender.Data.Setup.Keccak.ThetaRhoGeneric

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- The full imported theta/rho generic table has exactly one physical region
whose raw tag is the controller tag. -/
private theorem thetaRho_tag_column :
    thetaRhoGeneric.columns[8] =
      ⟨#[.affine 65536 4 0, .affine 524288 58 0, .affine 121 59 0,
          .affine 121 60 0, .affine 3604238 0 0]⟩ := by
  rfl

theorem thetaRho_controller_tag_region (i : Fin thetaRhoGeneric.length) :
    (thetaRhoGeneric.row i)[8] = 59 →
      589824 ≤ i.val ∧ i.val < 589945 := by
  intro h
  simp only [TableData.row, Vector.getElem_map] at h
  simp only [show thetaRhoGeneric.offset = 0 by rfl, Nat.zero_add] at h
  rw [thetaRho_tag_column] at h
  simp only [Column.get?, getFromBlocks, Block.get?, Block.length] at h
  split_ifs at h
  all_goals try simp only [zero_mul, add_zero] at h
  all_goals try simp [signedValue] at h
  all_goals try simp [babyBearModulus] at h
  all_goals omega

end Airbender.Keccak.Split.Native.Fixed.Proofs
