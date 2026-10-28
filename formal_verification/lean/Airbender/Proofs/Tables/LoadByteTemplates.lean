import Airbender.Data.Tables.Subword.LoadByteData
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def lowSignValues : Array Nat :=
  match (loadByteData.columns[1].blocks[1]? : Option Setup.Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]
def highSignValues : Array Nat :=
  match (loadByteData.columns[2].blocks[1]? : Option Setup.Block) with
  | some (.periodic _ _ values) => values
  | _ => #[]

theorem lowSign_size : lowSignValues.size = 256 := by decide +kernel
theorem highSign_size : highSignValues.size = 256 := by decide +kernel

theorem lowSign_samples (i : Fin 256) :
    lowSignValues[i.val]'(by rw [lowSign_size]; exact i.isLt) =
      if i.val < 128 then i.val else i.val + 65280 := by
  revert i
  decide +kernel

theorem highSign_samples (i : Fin 256) :
    highSignValues[i.val]'(by rw [highSign_size]; exact i.isLt) =
      if i.val < 128 then 65535 else 0 := by
  revert i
  decide +kernel

theorem byte_low_shape : loadByteData.columns[1] = Column.mk
    #[.periodic 256 0 (Array.range 256), .periodic 256 0 lowSignValues,
      .periodic 256 1 (Array.replicate 256 0),
      .periodic 128 1 (Array.replicate 256 0),
      .periodic 128 1 (Array.replicate 256 65408)] := rfl

theorem byte_high_shape : loadByteData.columns[2] = Column.mk
    #[.affine 65664 0 0, .periodic 256 0 highSignValues,
      .affine 98176 0 0, .affine 32768 65535 0] := rfl

end Airbender.Verification.SubwordFixed
