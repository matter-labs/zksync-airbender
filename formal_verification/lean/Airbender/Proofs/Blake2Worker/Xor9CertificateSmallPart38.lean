import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group184 : List Block := [dataT29Column2Block696,dataT29Column2Block697,dataT29Column2Block698,dataT29Column2Block699,dataT29Column2Block700,dataT29Column2Block701,dataT29Column2Block702,dataT29Column2Block703]

theorem length184 : (group184.map Block.length).sum = 128 := by
  simp [group184,dataT29Column2Block696,dataT29Column2Block697,dataT29Column2Block698,dataT29Column2Block699,dataT29Column2Block700,dataT29Column2Block701,dataT29Column2Block702,dataT29Column2Block703,Block.length]

theorem checked184 : checkBlocks (fun n => n/512 ^^^ n%512) 88944 group184 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group185 : List Block := [dataT29Column2Block704,dataT29Column2Block705,dataT29Column2Block706,dataT29Column2Block707,dataT29Column2Block708,dataT29Column2Block709,dataT29Column2Block710,dataT29Column2Block711]

theorem length185 : (group185.map Block.length).sum = 128 := by
  simp [group185,dataT29Column2Block704,dataT29Column2Block705,dataT29Column2Block706,dataT29Column2Block707,dataT29Column2Block708,dataT29Column2Block709,dataT29Column2Block710,dataT29Column2Block711,Block.length]

theorem checked185 : checkBlocks (fun n => n/512 ^^^ n%512) 89072 group185 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group186 : List Block := [dataT29Column2Block712,dataT29Column2Block713,dataT29Column2Block714,dataT29Column2Block715,dataT29Column2Block716,dataT29Column2Block717,dataT29Column2Block718,dataT29Column2Block719]

theorem length186 : (group186.map Block.length).sum = 128 := by
  simp [group186,dataT29Column2Block712,dataT29Column2Block713,dataT29Column2Block714,dataT29Column2Block715,dataT29Column2Block716,dataT29Column2Block717,dataT29Column2Block718,dataT29Column2Block719,Block.length]

theorem checked186 : checkBlocks (fun n => n/512 ^^^ n%512) 89200 group186 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group187 : List Block := [dataT29Column2Block720,dataT29Column2Block721,dataT29Column2Block722,dataT29Column2Block723,dataT29Column2Block724,dataT29Column2Block725,dataT29Column2Block726,dataT29Column2Block727]

theorem length187 : (group187.map Block.length).sum = 128 := by
  simp [group187,dataT29Column2Block720,dataT29Column2Block721,dataT29Column2Block722,dataT29Column2Block723,dataT29Column2Block724,dataT29Column2Block725,dataT29Column2Block726,dataT29Column2Block727,Block.length]

theorem checked187 : checkBlocks (fun n => n/512 ^^^ n%512) 89328 group187 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
