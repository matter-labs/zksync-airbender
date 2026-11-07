import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group196 : List Block := [dataT29Column2Block792,dataT29Column2Block793,dataT29Column2Block794,dataT29Column2Block795,dataT29Column2Block796,dataT29Column2Block797,dataT29Column2Block798,dataT29Column2Block799]

theorem length196 : (group196.map Block.length).sum = 512 := by
  simp [group196,dataT29Column2Block792,dataT29Column2Block793,dataT29Column2Block794,dataT29Column2Block795,dataT29Column2Block796,dataT29Column2Block797,dataT29Column2Block798,dataT29Column2Block799,Block.length]

theorem checked196 : checkBlocks (fun n => n/512 ^^^ n%512) 91584 group196 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group197 : List Block := [dataT29Column2Block800,dataT29Column2Block801,dataT29Column2Block802,dataT29Column2Block803,dataT29Column2Block804,dataT29Column2Block805,dataT29Column2Block806,dataT29Column2Block807]

theorem length197 : (group197.map Block.length).sum = 512 := by
  simp [group197,dataT29Column2Block800,dataT29Column2Block801,dataT29Column2Block802,dataT29Column2Block803,dataT29Column2Block804,dataT29Column2Block805,dataT29Column2Block806,dataT29Column2Block807,Block.length]

theorem checked197 : checkBlocks (fun n => n/512 ^^^ n%512) 92096 group197 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group198 : List Block := [dataT29Column2Block808,dataT29Column2Block809,dataT29Column2Block810,dataT29Column2Block811,dataT29Column2Block812,dataT29Column2Block813,dataT29Column2Block814,dataT29Column2Block815]

theorem length198 : (group198.map Block.length).sum = 512 := by
  simp [group198,dataT29Column2Block808,dataT29Column2Block809,dataT29Column2Block810,dataT29Column2Block811,dataT29Column2Block812,dataT29Column2Block813,dataT29Column2Block814,dataT29Column2Block815,Block.length]

theorem checked198 : checkBlocks (fun n => n/512 ^^^ n%512) 92608 group198 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group199 : List Block := [dataT29Column2Block816,dataT29Column2Block817,dataT29Column2Block818,dataT29Column2Block819,dataT29Column2Block820,dataT29Column2Block821,dataT29Column2Block822,dataT29Column2Block823]

theorem length199 : (group199.map Block.length).sum = 512 := by
  simp [group199,dataT29Column2Block816,dataT29Column2Block817,dataT29Column2Block818,dataT29Column2Block819,dataT29Column2Block820,dataT29Column2Block821,dataT29Column2Block822,dataT29Column2Block823,Block.length]

theorem checked199 : checkBlocks (fun n => n/512 ^^^ n%512) 93120 group199 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
