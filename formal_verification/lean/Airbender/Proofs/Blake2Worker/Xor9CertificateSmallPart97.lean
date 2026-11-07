import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group420 : List Block := [dataT29Column2Block1797,dataT29Column2Block1798,dataT29Column2Block1799,dataT29Column2Block1800]

theorem length420 : (group420.map Block.length).sum = 512 := by
  simp [group420,dataT29Column2Block1797,dataT29Column2Block1798,dataT29Column2Block1799,dataT29Column2Block1800,Block.length]

theorem checked420 : checkBlocks (fun n => n/512 ^^^ n%512) 180608 group420 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group421 : List Block := [dataT29Column2Block1801,dataT29Column2Block1802,dataT29Column2Block1803,dataT29Column2Block1804]

theorem length421 : (group421.map Block.length).sum = 512 := by
  simp [group421,dataT29Column2Block1801,dataT29Column2Block1802,dataT29Column2Block1803,dataT29Column2Block1804,Block.length]

theorem checked421 : checkBlocks (fun n => n/512 ^^^ n%512) 181120 group421 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group422 : List Block := [dataT29Column2Block1805,dataT29Column2Block1806,dataT29Column2Block1807,dataT29Column2Block1808]

theorem length422 : (group422.map Block.length).sum = 512 := by
  simp [group422,dataT29Column2Block1805,dataT29Column2Block1806,dataT29Column2Block1807,dataT29Column2Block1808,Block.length]

theorem checked422 : checkBlocks (fun n => n/512 ^^^ n%512) 181632 group422 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group423 : List Block := [dataT29Column2Block1809,dataT29Column2Block1810,dataT29Column2Block1811,dataT29Column2Block1812]

theorem length423 : (group423.map Block.length).sum = 512 := by
  simp [group423,dataT29Column2Block1809,dataT29Column2Block1810,dataT29Column2Block1811,dataT29Column2Block1812,Block.length]

theorem checked423 : checkBlocks (fun n => n/512 ^^^ n%512) 182144 group423 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
