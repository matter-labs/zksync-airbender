import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group280 : List Block := [dataT29Column2Block1037,dataT29Column2Block1038]

theorem length280 : (group280.map Block.length).sum = 512 := by
  simp [group280,dataT29Column2Block1037,dataT29Column2Block1038,Block.length]

theorem checked280 : checkBlocks (fun n => n/512 ^^^ n%512) 134144 group280 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group281 : List Block := [dataT29Column2Block1039,dataT29Column2Block1040]

theorem length281 : (group281.map Block.length).sum = 512 := by
  simp [group281,dataT29Column2Block1039,dataT29Column2Block1040,Block.length]

theorem checked281 : checkBlocks (fun n => n/512 ^^^ n%512) 134656 group281 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group282 : List Block := [dataT29Column2Block1041,dataT29Column2Block1042]

theorem length282 : (group282.map Block.length).sum = 512 := by
  simp [group282,dataT29Column2Block1041,dataT29Column2Block1042,Block.length]

theorem checked282 : checkBlocks (fun n => n/512 ^^^ n%512) 135168 group282 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group283 : List Block := [dataT29Column2Block1043,dataT29Column2Block1044]

theorem length283 : (group283.map Block.length).sum = 512 := by
  simp [group283,dataT29Column2Block1043,dataT29Column2Block1044,Block.length]

theorem checked283 : checkBlocks (fun n => n/512 ^^^ n%512) 135680 group283 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
