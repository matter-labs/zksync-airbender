import Airbender.Proofs.Blake2Worker.Xor9Dense512
import Mathlib.Tactic.FinCases
import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group160 : List Block := [dataT29Column2Block512]

theorem length160 : (group160.map Block.length).sum = 512 :=
  (singleton_length dataT29Column2Block512).trans Xor9Dense512.length

theorem checked160 : checkBlocks (fun n => n/512 ^^^ n%512) 87040 group160 = true :=
  check_singleton_of_size _ _ _ 512 Xor9Dense512.length Xor9Dense512.reads

def group161 : List Block := [dataT29Column2Block513,dataT29Column2Block514,dataT29Column2Block515,dataT29Column2Block516,dataT29Column2Block517,dataT29Column2Block518,dataT29Column2Block519,dataT29Column2Block520]

theorem length161 : (group161.map Block.length).sum = 32 := by
  decide +kernel

theorem checked161 : checkBlocks (fun n => n/512 ^^^ n%512) 87552 group161 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group162 : List Block := [dataT29Column2Block521,dataT29Column2Block522,dataT29Column2Block523,dataT29Column2Block524,dataT29Column2Block525,dataT29Column2Block526,dataT29Column2Block527,dataT29Column2Block528]

theorem length162 : (group162.map Block.length).sum = 32 := by
  decide +kernel

theorem checked162 : checkBlocks (fun n => n/512 ^^^ n%512) 87584 group162 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group163 : List Block := [dataT29Column2Block529,dataT29Column2Block530,dataT29Column2Block531,dataT29Column2Block532,dataT29Column2Block533,dataT29Column2Block534,dataT29Column2Block535,dataT29Column2Block536]

theorem length163 : (group163.map Block.length).sum = 32 := by
  decide +kernel

theorem checked163 : checkBlocks (fun n => n/512 ^^^ n%512) 87616 group163 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
