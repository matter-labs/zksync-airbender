import Airbender.Proofs.Blake2Worker.BlockCertificates
import Airbender.Review.Circuits.Blake2Worker.FixedData28

namespace Airbender.Blake2Worker.Xor7Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def group0 : List Block := [dataT28Column2Block0,dataT28Column2Block1,dataT28Column2Block2,dataT28Column2Block3,dataT28Column2Block4,dataT28Column2Block5,dataT28Column2Block6,dataT28Column2Block7,dataT28Column2Block8,dataT28Column2Block9,dataT28Column2Block10,dataT28Column2Block11,dataT28Column2Block12,dataT28Column2Block13,dataT28Column2Block14,dataT28Column2Block15]

theorem length0 : (group0.map Block.length).sum = 2048 := by
  simp [group0,dataT28Column2Block0,dataT28Column2Block1,dataT28Column2Block2,dataT28Column2Block3,dataT28Column2Block4,dataT28Column2Block5,dataT28Column2Block6,dataT28Column2Block7,dataT28Column2Block8,dataT28Column2Block9,dataT28Column2Block10,dataT28Column2Block11,dataT28Column2Block12,dataT28Column2Block13,dataT28Column2Block14,dataT28Column2Block15,Block.length]

theorem checked0 : checkBlocks (fun n => n/128 ^^^ n%128) 0 group0 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group1 : List Block := [dataT28Column2Block16,dataT28Column2Block17,dataT28Column2Block18,dataT28Column2Block19,dataT28Column2Block20,dataT28Column2Block21,dataT28Column2Block22,dataT28Column2Block23,dataT28Column2Block24,dataT28Column2Block25,dataT28Column2Block26,dataT28Column2Block27,dataT28Column2Block28,dataT28Column2Block29,dataT28Column2Block30,dataT28Column2Block31]

theorem length1 : (group1.map Block.length).sum = 2048 := by
  simp [group1,dataT28Column2Block16,dataT28Column2Block17,dataT28Column2Block18,dataT28Column2Block19,dataT28Column2Block20,dataT28Column2Block21,dataT28Column2Block22,dataT28Column2Block23,dataT28Column2Block24,dataT28Column2Block25,dataT28Column2Block26,dataT28Column2Block27,dataT28Column2Block28,dataT28Column2Block29,dataT28Column2Block30,dataT28Column2Block31,Block.length]

theorem checked1 : checkBlocks (fun n => n/128 ^^^ n%128) 2048 group1 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group2 : List Block := [dataT28Column2Block32,dataT28Column2Block33,dataT28Column2Block34,dataT28Column2Block35,dataT28Column2Block36,dataT28Column2Block37,dataT28Column2Block38,dataT28Column2Block39,dataT28Column2Block40,dataT28Column2Block41,dataT28Column2Block42,dataT28Column2Block43,dataT28Column2Block44,dataT28Column2Block45,dataT28Column2Block46,dataT28Column2Block47]

theorem length2 : (group2.map Block.length).sum = 512 := by
  simp [group2,dataT28Column2Block32,dataT28Column2Block33,dataT28Column2Block34,dataT28Column2Block35,dataT28Column2Block36,dataT28Column2Block37,dataT28Column2Block38,dataT28Column2Block39,dataT28Column2Block40,dataT28Column2Block41,dataT28Column2Block42,dataT28Column2Block43,dataT28Column2Block44,dataT28Column2Block45,dataT28Column2Block46,dataT28Column2Block47,Block.length]

theorem checked2 : checkBlocks (fun n => n/128 ^^^ n%128) 4096 group2 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group3 : List Block := [dataT28Column2Block48,dataT28Column2Block49,dataT28Column2Block50,dataT28Column2Block51,dataT28Column2Block52,dataT28Column2Block53,dataT28Column2Block54,dataT28Column2Block55,dataT28Column2Block56,dataT28Column2Block57,dataT28Column2Block58,dataT28Column2Block59,dataT28Column2Block60,dataT28Column2Block61,dataT28Column2Block62,dataT28Column2Block63,dataT28Column2Block64,dataT28Column2Block65,dataT28Column2Block66,dataT28Column2Block67,dataT28Column2Block68,dataT28Column2Block69,dataT28Column2Block70,dataT28Column2Block71,dataT28Column2Block72,dataT28Column2Block73,dataT28Column2Block74,dataT28Column2Block75,dataT28Column2Block76,dataT28Column2Block77,dataT28Column2Block78,dataT28Column2Block79]

theorem length3 : (group3.map Block.length).sum = 640 := by
  simp [group3,dataT28Column2Block48,dataT28Column2Block49,dataT28Column2Block50,dataT28Column2Block51,dataT28Column2Block52,dataT28Column2Block53,dataT28Column2Block54,dataT28Column2Block55,dataT28Column2Block56,dataT28Column2Block57,dataT28Column2Block58,dataT28Column2Block59,dataT28Column2Block60,dataT28Column2Block61,dataT28Column2Block62,dataT28Column2Block63,dataT28Column2Block64,dataT28Column2Block65,dataT28Column2Block66,dataT28Column2Block67,dataT28Column2Block68,dataT28Column2Block69,dataT28Column2Block70,dataT28Column2Block71,dataT28Column2Block72,dataT28Column2Block73,dataT28Column2Block74,dataT28Column2Block75,dataT28Column2Block76,dataT28Column2Block77,dataT28Column2Block78,dataT28Column2Block79,Block.length]

theorem checked3 : checkBlocks (fun n => n/128 ^^^ n%128) 4608 group3 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group4 : List Block := [dataT28Column2Block80,dataT28Column2Block81,dataT28Column2Block82,dataT28Column2Block83,dataT28Column2Block84,dataT28Column2Block85,dataT28Column2Block86,dataT28Column2Block87,dataT28Column2Block88,dataT28Column2Block89,dataT28Column2Block90,dataT28Column2Block91,dataT28Column2Block92,dataT28Column2Block93,dataT28Column2Block94,dataT28Column2Block95]

theorem length4 : (group4.map Block.length).sum = 128 := by
  simp [group4,dataT28Column2Block80,dataT28Column2Block81,dataT28Column2Block82,dataT28Column2Block83,dataT28Column2Block84,dataT28Column2Block85,dataT28Column2Block86,dataT28Column2Block87,dataT28Column2Block88,dataT28Column2Block89,dataT28Column2Block90,dataT28Column2Block91,dataT28Column2Block92,dataT28Column2Block93,dataT28Column2Block94,dataT28Column2Block95,Block.length]

theorem checked4 : checkBlocks (fun n => n/128 ^^^ n%128) 5248 group4 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group5 : List Block := [dataT28Column2Block96,dataT28Column2Block97,dataT28Column2Block98,dataT28Column2Block99,dataT28Column2Block100,dataT28Column2Block101,dataT28Column2Block102,dataT28Column2Block103,dataT28Column2Block104,dataT28Column2Block105,dataT28Column2Block106,dataT28Column2Block107,dataT28Column2Block108,dataT28Column2Block109,dataT28Column2Block110,dataT28Column2Block111,dataT28Column2Block112,dataT28Column2Block113,dataT28Column2Block114,dataT28Column2Block115,dataT28Column2Block116,dataT28Column2Block117,dataT28Column2Block118,dataT28Column2Block119,dataT28Column2Block120,dataT28Column2Block121,dataT28Column2Block122,dataT28Column2Block123,dataT28Column2Block124,dataT28Column2Block125,dataT28Column2Block126,dataT28Column2Block127]

theorem length5 : (group5.map Block.length).sum = 252 := by
  simp [group5,dataT28Column2Block96,dataT28Column2Block97,dataT28Column2Block98,dataT28Column2Block99,dataT28Column2Block100,dataT28Column2Block101,dataT28Column2Block102,dataT28Column2Block103,dataT28Column2Block104,dataT28Column2Block105,dataT28Column2Block106,dataT28Column2Block107,dataT28Column2Block108,dataT28Column2Block109,dataT28Column2Block110,dataT28Column2Block111,dataT28Column2Block112,dataT28Column2Block113,dataT28Column2Block114,dataT28Column2Block115,dataT28Column2Block116,dataT28Column2Block117,dataT28Column2Block118,dataT28Column2Block119,dataT28Column2Block120,dataT28Column2Block121,dataT28Column2Block122,dataT28Column2Block123,dataT28Column2Block124,dataT28Column2Block125,dataT28Column2Block126,dataT28Column2Block127,Block.length]

theorem checked5 : checkBlocks (fun n => n/128 ^^^ n%128) 5376 group5 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group6 : List Block := [dataT28Column2Block128,dataT28Column2Block129,dataT28Column2Block130,dataT28Column2Block131,dataT28Column2Block132,dataT28Column2Block133,dataT28Column2Block134,dataT28Column2Block135,dataT28Column2Block136,dataT28Column2Block137,dataT28Column2Block138,dataT28Column2Block139,dataT28Column2Block140,dataT28Column2Block141,dataT28Column2Block142,dataT28Column2Block143]

theorem length6 : (group6.map Block.length).sum = 244 := by
  simp [group6,dataT28Column2Block128,dataT28Column2Block129,dataT28Column2Block130,dataT28Column2Block131,dataT28Column2Block132,dataT28Column2Block133,dataT28Column2Block134,dataT28Column2Block135,dataT28Column2Block136,dataT28Column2Block137,dataT28Column2Block138,dataT28Column2Block139,dataT28Column2Block140,dataT28Column2Block141,dataT28Column2Block142,dataT28Column2Block143,Block.length]

theorem checked6 : checkBlocks (fun n => n/128 ^^^ n%128) 5628 group6 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

def group7 : List Block := [dataT28Column2Block144,dataT28Column2Block145,dataT28Column2Block146,dataT28Column2Block147,dataT28Column2Block148,dataT28Column2Block149,dataT28Column2Block150,dataT28Column2Block151,dataT28Column2Block152,dataT28Column2Block153,dataT28Column2Block154,dataT28Column2Block155,dataT28Column2Block156,dataT28Column2Block157,dataT28Column2Block158,dataT28Column2Block159,dataT28Column2Block160,dataT28Column2Block161,dataT28Column2Block162,dataT28Column2Block163,dataT28Column2Block164,dataT28Column2Block165,dataT28Column2Block166,dataT28Column2Block167,dataT28Column2Block168,dataT28Column2Block169,dataT28Column2Block170,dataT28Column2Block171,dataT28Column2Block172,dataT28Column2Block173,dataT28Column2Block174,dataT28Column2Block175]

theorem length7 : (group7.map Block.length).sum = 1232 := by
  simp [group7,dataT28Column2Block144,dataT28Column2Block145,dataT28Column2Block146,dataT28Column2Block147,dataT28Column2Block148,dataT28Column2Block149,dataT28Column2Block150,dataT28Column2Block151,dataT28Column2Block152,dataT28Column2Block153,dataT28Column2Block154,dataT28Column2Block155,dataT28Column2Block156,dataT28Column2Block157,dataT28Column2Block158,dataT28Column2Block159,dataT28Column2Block160,dataT28Column2Block161,dataT28Column2Block162,dataT28Column2Block163,dataT28Column2Block164,dataT28Column2Block165,dataT28Column2Block166,dataT28Column2Block167,dataT28Column2Block168,dataT28Column2Block169,dataT28Column2Block170,dataT28Column2Block171,dataT28Column2Block172,dataT28Column2Block173,dataT28Column2Block174,dataT28Column2Block175,Block.length]

theorem checked7 : checkBlocks (fun n => n/128 ^^^ n%128) 5872 group7 = true :=
  checkWindowBlocks_sound _ _ _ (by decide +kernel)

end Airbender.Blake2Worker.Xor7Certificate
