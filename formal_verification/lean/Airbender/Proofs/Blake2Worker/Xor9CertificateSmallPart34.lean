import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group168 : List Block := [dataT29Column2Block569,dataT29Column2Block570,dataT29Column2Block571,dataT29Column2Block572,dataT29Column2Block573,dataT29Column2Block574,dataT29Column2Block575]

theorem length168 : (group168.map Block.length).sum = 28 := by
  simp [group168,dataT29Column2Block569,dataT29Column2Block570,dataT29Column2Block571,dataT29Column2Block572,dataT29Column2Block573,dataT29Column2Block574,dataT29Column2Block575,Block.length]

theorem checked168 : checkBlocks (fun n => n/512 ^^^ n%512) 87776 group168 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group169 : List Block := [dataT29Column2Block576,dataT29Column2Block577,dataT29Column2Block578,dataT29Column2Block579,dataT29Column2Block580,dataT29Column2Block581,dataT29Column2Block582,dataT29Column2Block583]

theorem length169 : (group169.map Block.length).sum = 32 := by
  simp [group169,dataT29Column2Block576,dataT29Column2Block577,dataT29Column2Block578,dataT29Column2Block579,dataT29Column2Block580,dataT29Column2Block581,dataT29Column2Block582,dataT29Column2Block583,Block.length]

theorem checked169 : checkBlocks (fun n => n/512 ^^^ n%512) 87804 group169 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group170 : List Block := [dataT29Column2Block584,dataT29Column2Block585,dataT29Column2Block586,dataT29Column2Block587,dataT29Column2Block588,dataT29Column2Block589,dataT29Column2Block590,dataT29Column2Block591]

theorem length170 : (group170.map Block.length).sum = 32 := by
  simp [group170,dataT29Column2Block584,dataT29Column2Block585,dataT29Column2Block586,dataT29Column2Block587,dataT29Column2Block588,dataT29Column2Block589,dataT29Column2Block590,dataT29Column2Block591,Block.length]

theorem checked170 : checkBlocks (fun n => n/512 ^^^ n%512) 87836 group170 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group171 : List Block := [dataT29Column2Block592,dataT29Column2Block593,dataT29Column2Block594,dataT29Column2Block595,dataT29Column2Block596,dataT29Column2Block597,dataT29Column2Block598,dataT29Column2Block599]

theorem length171 : (group171.map Block.length).sum = 32 := by
  simp [group171,dataT29Column2Block592,dataT29Column2Block593,dataT29Column2Block594,dataT29Column2Block595,dataT29Column2Block596,dataT29Column2Block597,dataT29Column2Block598,dataT29Column2Block599,Block.length]

theorem checked171 : checkBlocks (fun n => n/512 ^^^ n%512) 87868 group171 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
