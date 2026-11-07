import Airbender.Review.Circuits.Blake2Worker.FixedData29
import Airbender.Proofs.Blake2Worker.BlockCertificates

namespace Airbender.Blake2Worker.Xor9Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group344 : List Block := [dataT29Column2Block1201,dataT29Column2Block1202,dataT29Column2Block1203,dataT29Column2Block1204,dataT29Column2Block1205,dataT29Column2Block1206,dataT29Column2Block1207,dataT29Column2Block1208]

theorem length344 : (group344.map Block.length).sum = 512 := by
  simp [group344,dataT29Column2Block1201,dataT29Column2Block1202,dataT29Column2Block1203,dataT29Column2Block1204,dataT29Column2Block1205,dataT29Column2Block1206,dataT29Column2Block1207,dataT29Column2Block1208,Block.length]

theorem checked344 : checkBlocks (fun n => n/512 ^^^ n%512) 166912 group344 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group345 : List Block := [dataT29Column2Block1209,dataT29Column2Block1210,dataT29Column2Block1211,dataT29Column2Block1212,dataT29Column2Block1213,dataT29Column2Block1214,dataT29Column2Block1215,dataT29Column2Block1216]

theorem length345 : (group345.map Block.length).sum = 512 := by
  simp [group345,dataT29Column2Block1209,dataT29Column2Block1210,dataT29Column2Block1211,dataT29Column2Block1212,dataT29Column2Block1213,dataT29Column2Block1214,dataT29Column2Block1215,dataT29Column2Block1216,Block.length]

theorem checked345 : checkBlocks (fun n => n/512 ^^^ n%512) 167424 group345 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group346 : List Block := [dataT29Column2Block1217,dataT29Column2Block1218,dataT29Column2Block1219,dataT29Column2Block1220,dataT29Column2Block1221,dataT29Column2Block1222,dataT29Column2Block1223,dataT29Column2Block1224]

theorem length346 : (group346.map Block.length).sum = 512 := by
  simp [group346,dataT29Column2Block1217,dataT29Column2Block1218,dataT29Column2Block1219,dataT29Column2Block1220,dataT29Column2Block1221,dataT29Column2Block1222,dataT29Column2Block1223,dataT29Column2Block1224,Block.length]

theorem checked346 : checkBlocks (fun n => n/512 ^^^ n%512) 167936 group346 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group347 : List Block := [dataT29Column2Block1225,dataT29Column2Block1226,dataT29Column2Block1227,dataT29Column2Block1228,dataT29Column2Block1229,dataT29Column2Block1230,dataT29Column2Block1231,dataT29Column2Block1232]

theorem length347 : (group347.map Block.length).sum = 512 := by
  simp [group347,dataT29Column2Block1225,dataT29Column2Block1226,dataT29Column2Block1227,dataT29Column2Block1228,dataT29Column2Block1229,dataT29Column2Block1230,dataT29Column2Block1231,dataT29Column2Block1232,Block.length]

theorem checked347 : checkBlocks (fun n => n/512 ^^^ n%512) 168448 group347 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor9Certificate
