import Airbender.Proofs.FullUnsigned.SourceFirstBlocks
import Airbender.Proofs.FullUnsigned.Source.Theta
import Airbender.Proofs.Keccak.SplitThetaFragmentValues

namespace Airbender.Setup.SourceCaptureThetaProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn : Column := (SourceCaptureTheta.columns[4]?).getD ⟨#[]⟩
private theorem source_head : sourceColumn.blocks.toList.head? = some (.affine 131200 0 0) := by
  setup_source_rfl

/-- The complete source overflow fragment is zero for shift zero. -/
theorem source_split_high_zero_get (index : Fin 65536) :
    ((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val) = some 0 := by
  exact (getFromBlocks_first _ _ _ source_head (by change 65536 + index.val < 131200; omega)).trans
    (constant_affine_get _ _ _ (by omega))

/-- The source overflow equals its complete original native value. -/
theorem source_split_high_zero_match (index : Fin 65536) :
    (((SourceCaptureTheta.columns[4]?).getD ({ blocks := #[] } : Column)).get? (65536 + index.val)).getD 0 =
      (Airbender.Keccak.Split.Native.Fixed.thetaRhoXorSplit.columns[4]).value index.val := by
  rw [source_split_high_zero_get, Option.getD_some]
  have native := Airbender.Keccak.Split.Native.Fixed.Proofs.theta_fragment_high_value
    ⟨index.val, by change index.val < 524288; have bound := index.isLt; omega⟩
  have shift : index.val / 65536 = 0 := by omega
  rw [shift] at native
  change _ = ((index.val / 256 % 256) ^^^ (index.val % 256)) / 256 at native
  rw [native]
  have bound : ((index.val / 256 % 256) ^^^ (index.val % 256)) < 256 := by
    exact Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  exact (Nat.div_eq_of_lt bound).symm

end Airbender.Setup.SourceCaptureThetaProofs
