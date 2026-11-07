import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group300 : List Block := [dataT29Column2Block1077,dataT29Column2Block1078]

theorem length300 : (group300.map Block.length).sum = 512 := by
  simp [group300,dataT29Column2Block1077,dataT29Column2Block1078,Block.length]

theorem checked300 : checkBlocks (fun n => n/512 ^^^ n%512) 144384 group300 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group301 : List Block := [dataT29Column2Block1079,dataT29Column2Block1080]

theorem length301 : (group301.map Block.length).sum = 512 := by
  simp [group301,dataT29Column2Block1079,dataT29Column2Block1080,Block.length]

theorem checked301 : checkBlocks (fun n => n/512 ^^^ n%512) 144896 group301 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group302 : List Block := [dataT29Column2Block1081,dataT29Column2Block1082]

theorem length302 : (group302.map Block.length).sum = 512 := by
  simp [group302,dataT29Column2Block1081,dataT29Column2Block1082,Block.length]

theorem checked302 : checkBlocks (fun n => n/512 ^^^ n%512) 145408 group302 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group303 : List Block := [dataT29Column2Block1083,dataT29Column2Block1084]

theorem length303 : (group303.map Block.length).sum = 512 := by
  simp [group303,dataT29Column2Block1083,dataT29Column2Block1084,Block.length]

theorem checked303 : checkBlocks (fun n => n/512 ^^^ n%512) 145920 group303 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
