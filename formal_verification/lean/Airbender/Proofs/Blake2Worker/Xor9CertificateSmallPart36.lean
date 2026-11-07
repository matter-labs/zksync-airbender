import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group176 : List Block := [dataT29Column2Block632,dataT29Column2Block633,dataT29Column2Block634,dataT29Column2Block635,dataT29Column2Block636,dataT29Column2Block637,dataT29Column2Block638,dataT29Column2Block639]

theorem length176 : (group176.map Block.length).sum = 32 := by
  simp [group176,dataT29Column2Block632,dataT29Column2Block633,dataT29Column2Block634,dataT29Column2Block635,dataT29Column2Block636,dataT29Column2Block637,dataT29Column2Block638,dataT29Column2Block639,Block.length]

theorem checked176 : checkBlocks (fun n => n/512 ^^^ n%512) 88028 group176 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group177 : List Block := [dataT29Column2Block640,dataT29Column2Block641,dataT29Column2Block642,dataT29Column2Block643,dataT29Column2Block644,dataT29Column2Block645,dataT29Column2Block646,dataT29Column2Block647]

theorem length177 : (group177.map Block.length).sum = 116 := by
  simp [group177,dataT29Column2Block640,dataT29Column2Block641,dataT29Column2Block642,dataT29Column2Block643,dataT29Column2Block644,dataT29Column2Block645,dataT29Column2Block646,dataT29Column2Block647,Block.length]

theorem checked177 : checkBlocks (fun n => n/512 ^^^ n%512) 88060 group177 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group178 : List Block := [dataT29Column2Block648,dataT29Column2Block649,dataT29Column2Block650,dataT29Column2Block651,dataT29Column2Block652,dataT29Column2Block653,dataT29Column2Block654,dataT29Column2Block655]

theorem length178 : (group178.map Block.length).sum = 128 := by
  simp [group178,dataT29Column2Block648,dataT29Column2Block649,dataT29Column2Block650,dataT29Column2Block651,dataT29Column2Block652,dataT29Column2Block653,dataT29Column2Block654,dataT29Column2Block655,Block.length]

theorem checked178 : checkBlocks (fun n => n/512 ^^^ n%512) 88176 group178 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group179 : List Block := [dataT29Column2Block656,dataT29Column2Block657,dataT29Column2Block658,dataT29Column2Block659,dataT29Column2Block660,dataT29Column2Block661,dataT29Column2Block662,dataT29Column2Block663]

theorem length179 : (group179.map Block.length).sum = 128 := by
  simp [group179,dataT29Column2Block656,dataT29Column2Block657,dataT29Column2Block658,dataT29Column2Block659,dataT29Column2Block660,dataT29Column2Block661,dataT29Column2Block662,dataT29Column2Block663,Block.length]

theorem checked179 : checkBlocks (fun n => n/512 ^^^ n%512) 88304 group179 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
