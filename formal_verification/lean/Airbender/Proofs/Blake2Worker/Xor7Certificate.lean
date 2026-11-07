import Airbender.Proofs.Blake2Worker.Xor7CertificatePart0
import Airbender.Proofs.Blake2Worker.Xor7CertificatePart1
import Airbender.Proofs.Blake2Worker.Xor7CertificatePart2
import Airbender.Proofs.Mersenne31

namespace Airbender.Blake2Worker.Xor7Certificate
open Setup Setup.Proofs Fixed
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem leafLength0 : ([dataT28Column2Block0,dataT28Column2Block1,dataT28Column2Block2,dataT28Column2Block3,dataT28Column2Block4,dataT28Column2Block5,dataT28Column2Block6,dataT28Column2Block7,dataT28Column2Block8,dataT28Column2Block9,dataT28Column2Block10,dataT28Column2Block11,dataT28Column2Block12,dataT28Column2Block13,dataT28Column2Block14,dataT28Column2Block15,dataT28Column2Block16,dataT28Column2Block17,dataT28Column2Block18,dataT28Column2Block19,dataT28Column2Block20,dataT28Column2Block21,dataT28Column2Block22,dataT28Column2Block23,dataT28Column2Block24,dataT28Column2Block25,dataT28Column2Block26,dataT28Column2Block27,dataT28Column2Block28,dataT28Column2Block29,dataT28Column2Block30,dataT28Column2Block31,dataT28Column2Block32,dataT28Column2Block33,dataT28Column2Block34,dataT28Column2Block35,dataT28Column2Block36,dataT28Column2Block37,dataT28Column2Block38,dataT28Column2Block39,dataT28Column2Block40,dataT28Column2Block41,dataT28Column2Block42,dataT28Column2Block43,dataT28Column2Block44,dataT28Column2Block45,dataT28Column2Block46,dataT28Column2Block47].map Block.length).sum = 4608 := by
  change ((group0 ++ group1 ++ group2).map Block.length).sum = 4608
  simp only [List.map_append,List.sum_append,length0,length1,length2,Nat.reduceAdd]

theorem leafChecked0 : checkBlocks (fun n => n/128 ^^^ n%128) 0 [dataT28Column2Block0,dataT28Column2Block1,dataT28Column2Block2,dataT28Column2Block3,dataT28Column2Block4,dataT28Column2Block5,dataT28Column2Block6,dataT28Column2Block7,dataT28Column2Block8,dataT28Column2Block9,dataT28Column2Block10,dataT28Column2Block11,dataT28Column2Block12,dataT28Column2Block13,dataT28Column2Block14,dataT28Column2Block15,dataT28Column2Block16,dataT28Column2Block17,dataT28Column2Block18,dataT28Column2Block19,dataT28Column2Block20,dataT28Column2Block21,dataT28Column2Block22,dataT28Column2Block23,dataT28Column2Block24,dataT28Column2Block25,dataT28Column2Block26,dataT28Column2Block27,dataT28Column2Block28,dataT28Column2Block29,dataT28Column2Block30,dataT28Column2Block31,dataT28Column2Block32,dataT28Column2Block33,dataT28Column2Block34,dataT28Column2Block35,dataT28Column2Block36,dataT28Column2Block37,dataT28Column2Block38,dataT28Column2Block39,dataT28Column2Block40,dataT28Column2Block41,dataT28Column2Block42,dataT28Column2Block43,dataT28Column2Block44,dataT28Column2Block45,dataT28Column2Block46,dataT28Column2Block47] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 0 (group0 ++ group1 ++ group2) = true
  simp only [checkBlocks_append_iff]
  simp only [List.map_append,List.sum_append]
  simp only [length0,length1,Nat.reduceAdd]
  exact ⟨⟨checked0,checked1⟩,checked2⟩

theorem leafLength1 : ([dataT28Column2Block48,dataT28Column2Block49,dataT28Column2Block50,dataT28Column2Block51,dataT28Column2Block52,dataT28Column2Block53,dataT28Column2Block54,dataT28Column2Block55,dataT28Column2Block56,dataT28Column2Block57,dataT28Column2Block58,dataT28Column2Block59,dataT28Column2Block60,dataT28Column2Block61,dataT28Column2Block62,dataT28Column2Block63,dataT28Column2Block64,dataT28Column2Block65,dataT28Column2Block66,dataT28Column2Block67,dataT28Column2Block68,dataT28Column2Block69,dataT28Column2Block70,dataT28Column2Block71,dataT28Column2Block72,dataT28Column2Block73,dataT28Column2Block74,dataT28Column2Block75,dataT28Column2Block76,dataT28Column2Block77,dataT28Column2Block78,dataT28Column2Block79,dataT28Column2Block80,dataT28Column2Block81,dataT28Column2Block82,dataT28Column2Block83,dataT28Column2Block84,dataT28Column2Block85,dataT28Column2Block86,dataT28Column2Block87,dataT28Column2Block88,dataT28Column2Block89,dataT28Column2Block90,dataT28Column2Block91,dataT28Column2Block92,dataT28Column2Block93,dataT28Column2Block94,dataT28Column2Block95].map Block.length).sum = 768 := by
  change ((group3 ++ group4).map Block.length).sum = 768
  simp only [List.map_append,List.sum_append,length3,length4,Nat.reduceAdd]

theorem leafChecked1 : checkBlocks (fun n => n/128 ^^^ n%128) 4608 [dataT28Column2Block48,dataT28Column2Block49,dataT28Column2Block50,dataT28Column2Block51,dataT28Column2Block52,dataT28Column2Block53,dataT28Column2Block54,dataT28Column2Block55,dataT28Column2Block56,dataT28Column2Block57,dataT28Column2Block58,dataT28Column2Block59,dataT28Column2Block60,dataT28Column2Block61,dataT28Column2Block62,dataT28Column2Block63,dataT28Column2Block64,dataT28Column2Block65,dataT28Column2Block66,dataT28Column2Block67,dataT28Column2Block68,dataT28Column2Block69,dataT28Column2Block70,dataT28Column2Block71,dataT28Column2Block72,dataT28Column2Block73,dataT28Column2Block74,dataT28Column2Block75,dataT28Column2Block76,dataT28Column2Block77,dataT28Column2Block78,dataT28Column2Block79,dataT28Column2Block80,dataT28Column2Block81,dataT28Column2Block82,dataT28Column2Block83,dataT28Column2Block84,dataT28Column2Block85,dataT28Column2Block86,dataT28Column2Block87,dataT28Column2Block88,dataT28Column2Block89,dataT28Column2Block90,dataT28Column2Block91,dataT28Column2Block92,dataT28Column2Block93,dataT28Column2Block94,dataT28Column2Block95] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 4608 (group3 ++ group4) = true
  simp only [checkBlocks_append_iff]
  simp only [length3,Nat.reduceAdd]
  exact ⟨checked3,checked4⟩

theorem leafLength2 : ([dataT28Column2Block96,dataT28Column2Block97,dataT28Column2Block98,dataT28Column2Block99,dataT28Column2Block100,dataT28Column2Block101,dataT28Column2Block102,dataT28Column2Block103,dataT28Column2Block104,dataT28Column2Block105,dataT28Column2Block106,dataT28Column2Block107,dataT28Column2Block108,dataT28Column2Block109,dataT28Column2Block110,dataT28Column2Block111,dataT28Column2Block112,dataT28Column2Block113,dataT28Column2Block114,dataT28Column2Block115,dataT28Column2Block116,dataT28Column2Block117,dataT28Column2Block118,dataT28Column2Block119,dataT28Column2Block120,dataT28Column2Block121,dataT28Column2Block122,dataT28Column2Block123,dataT28Column2Block124,dataT28Column2Block125,dataT28Column2Block126,dataT28Column2Block127,dataT28Column2Block128,dataT28Column2Block129,dataT28Column2Block130,dataT28Column2Block131,dataT28Column2Block132,dataT28Column2Block133,dataT28Column2Block134,dataT28Column2Block135,dataT28Column2Block136,dataT28Column2Block137,dataT28Column2Block138,dataT28Column2Block139,dataT28Column2Block140,dataT28Column2Block141,dataT28Column2Block142,dataT28Column2Block143].map Block.length).sum = 496 := by
  change ((group5 ++ group6).map Block.length).sum = 496
  simp only [List.map_append,List.sum_append,length5,length6,Nat.reduceAdd]

theorem leafChecked2 : checkBlocks (fun n => n/128 ^^^ n%128) 5376 [dataT28Column2Block96,dataT28Column2Block97,dataT28Column2Block98,dataT28Column2Block99,dataT28Column2Block100,dataT28Column2Block101,dataT28Column2Block102,dataT28Column2Block103,dataT28Column2Block104,dataT28Column2Block105,dataT28Column2Block106,dataT28Column2Block107,dataT28Column2Block108,dataT28Column2Block109,dataT28Column2Block110,dataT28Column2Block111,dataT28Column2Block112,dataT28Column2Block113,dataT28Column2Block114,dataT28Column2Block115,dataT28Column2Block116,dataT28Column2Block117,dataT28Column2Block118,dataT28Column2Block119,dataT28Column2Block120,dataT28Column2Block121,dataT28Column2Block122,dataT28Column2Block123,dataT28Column2Block124,dataT28Column2Block125,dataT28Column2Block126,dataT28Column2Block127,dataT28Column2Block128,dataT28Column2Block129,dataT28Column2Block130,dataT28Column2Block131,dataT28Column2Block132,dataT28Column2Block133,dataT28Column2Block134,dataT28Column2Block135,dataT28Column2Block136,dataT28Column2Block137,dataT28Column2Block138,dataT28Column2Block139,dataT28Column2Block140,dataT28Column2Block141,dataT28Column2Block142,dataT28Column2Block143] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 5376 (group5 ++ group6) = true
  simp only [checkBlocks_append_iff]
  simp only [length5,Nat.reduceAdd]
  exact ⟨checked5,checked6⟩

theorem leafLength3 : ([dataT28Column2Block144,dataT28Column2Block145,dataT28Column2Block146,dataT28Column2Block147,dataT28Column2Block148,dataT28Column2Block149,dataT28Column2Block150,dataT28Column2Block151,dataT28Column2Block152,dataT28Column2Block153,dataT28Column2Block154,dataT28Column2Block155,dataT28Column2Block156,dataT28Column2Block157,dataT28Column2Block158,dataT28Column2Block159,dataT28Column2Block160,dataT28Column2Block161,dataT28Column2Block162,dataT28Column2Block163,dataT28Column2Block164,dataT28Column2Block165,dataT28Column2Block166,dataT28Column2Block167,dataT28Column2Block168,dataT28Column2Block169,dataT28Column2Block170,dataT28Column2Block171,dataT28Column2Block172,dataT28Column2Block173,dataT28Column2Block174,dataT28Column2Block175,dataT28Column2Block176,dataT28Column2Block177,dataT28Column2Block178,dataT28Column2Block179,dataT28Column2Block180,dataT28Column2Block181,dataT28Column2Block182,dataT28Column2Block183,dataT28Column2Block184,dataT28Column2Block185,dataT28Column2Block186,dataT28Column2Block187,dataT28Column2Block188,dataT28Column2Block189,dataT28Column2Block190,dataT28Column2Block191,dataT28Column2Block192].map Block.length).sum = 2320 := by
  change ((group7 ++ group8).map Block.length).sum = 2320
  simp only [List.map_append,List.sum_append,length7,length8,Nat.reduceAdd]

theorem leafChecked3 : checkBlocks (fun n => n/128 ^^^ n%128) 5872 [dataT28Column2Block144,dataT28Column2Block145,dataT28Column2Block146,dataT28Column2Block147,dataT28Column2Block148,dataT28Column2Block149,dataT28Column2Block150,dataT28Column2Block151,dataT28Column2Block152,dataT28Column2Block153,dataT28Column2Block154,dataT28Column2Block155,dataT28Column2Block156,dataT28Column2Block157,dataT28Column2Block158,dataT28Column2Block159,dataT28Column2Block160,dataT28Column2Block161,dataT28Column2Block162,dataT28Column2Block163,dataT28Column2Block164,dataT28Column2Block165,dataT28Column2Block166,dataT28Column2Block167,dataT28Column2Block168,dataT28Column2Block169,dataT28Column2Block170,dataT28Column2Block171,dataT28Column2Block172,dataT28Column2Block173,dataT28Column2Block174,dataT28Column2Block175,dataT28Column2Block176,dataT28Column2Block177,dataT28Column2Block178,dataT28Column2Block179,dataT28Column2Block180,dataT28Column2Block181,dataT28Column2Block182,dataT28Column2Block183,dataT28Column2Block184,dataT28Column2Block185,dataT28Column2Block186,dataT28Column2Block187,dataT28Column2Block188,dataT28Column2Block189,dataT28Column2Block190,dataT28Column2Block191,dataT28Column2Block192] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 5872 (group7 ++ group8) = true
  simp only [checkBlocks_append_iff]
  simp only [length7,Nat.reduceAdd]
  exact ⟨checked7,checked8⟩

theorem leafLength4 : ([dataT28Column2Block193,dataT28Column2Block194,dataT28Column2Block195,dataT28Column2Block196,dataT28Column2Block197,dataT28Column2Block198,dataT28Column2Block199,dataT28Column2Block200,dataT28Column2Block201,dataT28Column2Block202,dataT28Column2Block203,dataT28Column2Block204,dataT28Column2Block205,dataT28Column2Block206,dataT28Column2Block207,dataT28Column2Block208,dataT28Column2Block209,dataT28Column2Block210,dataT28Column2Block211,dataT28Column2Block212,dataT28Column2Block213,dataT28Column2Block214,dataT28Column2Block215,dataT28Column2Block216,dataT28Column2Block217,dataT28Column2Block218,dataT28Column2Block219,dataT28Column2Block220,dataT28Column2Block221,dataT28Column2Block222,dataT28Column2Block223,dataT28Column2Block224,dataT28Column2Block225,dataT28Column2Block226,dataT28Column2Block227,dataT28Column2Block228,dataT28Column2Block229,dataT28Column2Block230,dataT28Column2Block231,dataT28Column2Block232,dataT28Column2Block233,dataT28Column2Block234,dataT28Column2Block235,dataT28Column2Block236,dataT28Column2Block237,dataT28Column2Block238,dataT28Column2Block239,dataT28Column2Block240].map Block.length).sum = 2304 := by
  change ((group9 ++ group10).map Block.length).sum = 2304
  simp only [List.map_append,List.sum_append,length9,length10,Nat.reduceAdd]

theorem leafChecked4 : checkBlocks (fun n => n/128 ^^^ n%128) 8192 [dataT28Column2Block193,dataT28Column2Block194,dataT28Column2Block195,dataT28Column2Block196,dataT28Column2Block197,dataT28Column2Block198,dataT28Column2Block199,dataT28Column2Block200,dataT28Column2Block201,dataT28Column2Block202,dataT28Column2Block203,dataT28Column2Block204,dataT28Column2Block205,dataT28Column2Block206,dataT28Column2Block207,dataT28Column2Block208,dataT28Column2Block209,dataT28Column2Block210,dataT28Column2Block211,dataT28Column2Block212,dataT28Column2Block213,dataT28Column2Block214,dataT28Column2Block215,dataT28Column2Block216,dataT28Column2Block217,dataT28Column2Block218,dataT28Column2Block219,dataT28Column2Block220,dataT28Column2Block221,dataT28Column2Block222,dataT28Column2Block223,dataT28Column2Block224,dataT28Column2Block225,dataT28Column2Block226,dataT28Column2Block227,dataT28Column2Block228,dataT28Column2Block229,dataT28Column2Block230,dataT28Column2Block231,dataT28Column2Block232,dataT28Column2Block233,dataT28Column2Block234,dataT28Column2Block235,dataT28Column2Block236,dataT28Column2Block237,dataT28Column2Block238,dataT28Column2Block239,dataT28Column2Block240] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 8192 (group9 ++ group10) = true
  simp only [checkBlocks_append_iff]
  simp only [length9,Nat.reduceAdd]
  exact ⟨checked9,checked10⟩

theorem leafLength5 : ([dataT28Column2Block241,dataT28Column2Block242,dataT28Column2Block243,dataT28Column2Block244,dataT28Column2Block245,dataT28Column2Block246,dataT28Column2Block247,dataT28Column2Block248,dataT28Column2Block249,dataT28Column2Block250,dataT28Column2Block251,dataT28Column2Block252,dataT28Column2Block253,dataT28Column2Block254,dataT28Column2Block255,dataT28Column2Block256,dataT28Column2Block257,dataT28Column2Block258,dataT28Column2Block259,dataT28Column2Block260,dataT28Column2Block261,dataT28Column2Block262,dataT28Column2Block263,dataT28Column2Block264,dataT28Column2Block265,dataT28Column2Block266,dataT28Column2Block267,dataT28Column2Block268,dataT28Column2Block269,dataT28Column2Block270,dataT28Column2Block271,dataT28Column2Block272,dataT28Column2Block273,dataT28Column2Block274,dataT28Column2Block275,dataT28Column2Block276,dataT28Column2Block277,dataT28Column2Block278,dataT28Column2Block279,dataT28Column2Block280,dataT28Column2Block281,dataT28Column2Block282,dataT28Column2Block283,dataT28Column2Block284,dataT28Column2Block285,dataT28Column2Block286,dataT28Column2Block287,dataT28Column2Block288].map Block.length).sum = 384 := by
  change ((group11 ++ group12).map Block.length).sum = 384
  simp only [List.map_append,List.sum_append,length11,length12,Nat.reduceAdd]

theorem leafChecked5 : checkBlocks (fun n => n/128 ^^^ n%128) 10496 [dataT28Column2Block241,dataT28Column2Block242,dataT28Column2Block243,dataT28Column2Block244,dataT28Column2Block245,dataT28Column2Block246,dataT28Column2Block247,dataT28Column2Block248,dataT28Column2Block249,dataT28Column2Block250,dataT28Column2Block251,dataT28Column2Block252,dataT28Column2Block253,dataT28Column2Block254,dataT28Column2Block255,dataT28Column2Block256,dataT28Column2Block257,dataT28Column2Block258,dataT28Column2Block259,dataT28Column2Block260,dataT28Column2Block261,dataT28Column2Block262,dataT28Column2Block263,dataT28Column2Block264,dataT28Column2Block265,dataT28Column2Block266,dataT28Column2Block267,dataT28Column2Block268,dataT28Column2Block269,dataT28Column2Block270,dataT28Column2Block271,dataT28Column2Block272,dataT28Column2Block273,dataT28Column2Block274,dataT28Column2Block275,dataT28Column2Block276,dataT28Column2Block277,dataT28Column2Block278,dataT28Column2Block279,dataT28Column2Block280,dataT28Column2Block281,dataT28Column2Block282,dataT28Column2Block283,dataT28Column2Block284,dataT28Column2Block285,dataT28Column2Block286,dataT28Column2Block287,dataT28Column2Block288] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 10496 (group11 ++ group12) = true
  simp only [checkBlocks_append_iff]
  simp only [length11,Nat.reduceAdd]
  exact ⟨checked11,checked12⟩

theorem leafLength6 : ([dataT28Column2Block289,dataT28Column2Block290,dataT28Column2Block291,dataT28Column2Block292,dataT28Column2Block293,dataT28Column2Block294,dataT28Column2Block295,dataT28Column2Block296,dataT28Column2Block297,dataT28Column2Block298,dataT28Column2Block299,dataT28Column2Block300,dataT28Column2Block301,dataT28Column2Block302,dataT28Column2Block303,dataT28Column2Block304,dataT28Column2Block305,dataT28Column2Block306,dataT28Column2Block307,dataT28Column2Block308,dataT28Column2Block309,dataT28Column2Block310,dataT28Column2Block311,dataT28Column2Block312,dataT28Column2Block313,dataT28Column2Block314,dataT28Column2Block315,dataT28Column2Block316,dataT28Column2Block317,dataT28Column2Block318,dataT28Column2Block319,dataT28Column2Block320,dataT28Column2Block321,dataT28Column2Block322,dataT28Column2Block323,dataT28Column2Block324,dataT28Column2Block325,dataT28Column2Block326,dataT28Column2Block327,dataT28Column2Block328,dataT28Column2Block329,dataT28Column2Block330,dataT28Column2Block331,dataT28Column2Block332,dataT28Column2Block333,dataT28Column2Block334,dataT28Column2Block335,dataT28Column2Block336].map Block.length).sum = 864 := by
  change ((group13 ++ group14).map Block.length).sum = 864
  simp only [List.map_append,List.sum_append,length13,length14,Nat.reduceAdd]

theorem leafChecked6 : checkBlocks (fun n => n/128 ^^^ n%128) 10880 [dataT28Column2Block289,dataT28Column2Block290,dataT28Column2Block291,dataT28Column2Block292,dataT28Column2Block293,dataT28Column2Block294,dataT28Column2Block295,dataT28Column2Block296,dataT28Column2Block297,dataT28Column2Block298,dataT28Column2Block299,dataT28Column2Block300,dataT28Column2Block301,dataT28Column2Block302,dataT28Column2Block303,dataT28Column2Block304,dataT28Column2Block305,dataT28Column2Block306,dataT28Column2Block307,dataT28Column2Block308,dataT28Column2Block309,dataT28Column2Block310,dataT28Column2Block311,dataT28Column2Block312,dataT28Column2Block313,dataT28Column2Block314,dataT28Column2Block315,dataT28Column2Block316,dataT28Column2Block317,dataT28Column2Block318,dataT28Column2Block319,dataT28Column2Block320,dataT28Column2Block321,dataT28Column2Block322,dataT28Column2Block323,dataT28Column2Block324,dataT28Column2Block325,dataT28Column2Block326,dataT28Column2Block327,dataT28Column2Block328,dataT28Column2Block329,dataT28Column2Block330,dataT28Column2Block331,dataT28Column2Block332,dataT28Column2Block333,dataT28Column2Block334,dataT28Column2Block335,dataT28Column2Block336] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 10880 (group13 ++ group14) = true
  simp only [checkBlocks_append_iff]
  simp only [length13,Nat.reduceAdd]
  exact ⟨checked13,checked14⟩

theorem leafLength7 : ([dataT28Column2Block337,dataT28Column2Block338,dataT28Column2Block339,dataT28Column2Block340,dataT28Column2Block341,dataT28Column2Block342,dataT28Column2Block343,dataT28Column2Block344,dataT28Column2Block345,dataT28Column2Block346,dataT28Column2Block347,dataT28Column2Block348,dataT28Column2Block349,dataT28Column2Block350,dataT28Column2Block351,dataT28Column2Block352,dataT28Column2Block353,dataT28Column2Block354,dataT28Column2Block355,dataT28Column2Block356,dataT28Column2Block357,dataT28Column2Block358,dataT28Column2Block359,dataT28Column2Block360,dataT28Column2Block361,dataT28Column2Block362,dataT28Column2Block363,dataT28Column2Block364,dataT28Column2Block365,dataT28Column2Block366,dataT28Column2Block367,dataT28Column2Block368,dataT28Column2Block369,dataT28Column2Block370,dataT28Column2Block371,dataT28Column2Block372,dataT28Column2Block373,dataT28Column2Block374,dataT28Column2Block375,dataT28Column2Block376,dataT28Column2Block377,dataT28Column2Block378,dataT28Column2Block379,dataT28Column2Block380,dataT28Column2Block381,dataT28Column2Block382,dataT28Column2Block383,dataT28Column2Block384,dataT28Column2Block385].map Block.length).sum = 4640 := by
  change ((group15 ++ group16 ++ group17).map Block.length).sum = 4640
  simp only [List.map_append,List.sum_append,length15,length16,length17,Nat.reduceAdd]

theorem leafChecked7 : checkBlocks (fun n => n/128 ^^^ n%128) 11744 [dataT28Column2Block337,dataT28Column2Block338,dataT28Column2Block339,dataT28Column2Block340,dataT28Column2Block341,dataT28Column2Block342,dataT28Column2Block343,dataT28Column2Block344,dataT28Column2Block345,dataT28Column2Block346,dataT28Column2Block347,dataT28Column2Block348,dataT28Column2Block349,dataT28Column2Block350,dataT28Column2Block351,dataT28Column2Block352,dataT28Column2Block353,dataT28Column2Block354,dataT28Column2Block355,dataT28Column2Block356,dataT28Column2Block357,dataT28Column2Block358,dataT28Column2Block359,dataT28Column2Block360,dataT28Column2Block361,dataT28Column2Block362,dataT28Column2Block363,dataT28Column2Block364,dataT28Column2Block365,dataT28Column2Block366,dataT28Column2Block367,dataT28Column2Block368,dataT28Column2Block369,dataT28Column2Block370,dataT28Column2Block371,dataT28Column2Block372,dataT28Column2Block373,dataT28Column2Block374,dataT28Column2Block375,dataT28Column2Block376,dataT28Column2Block377,dataT28Column2Block378,dataT28Column2Block379,dataT28Column2Block380,dataT28Column2Block381,dataT28Column2Block382,dataT28Column2Block383,dataT28Column2Block384,dataT28Column2Block385] = true := by
  change checkBlocks (fun n => n/128 ^^^ n%128) 11744 (group15 ++ group16 ++ group17) = true
  simp only [checkBlocks_append_iff]
  simp only [List.map_append,List.sum_append]
  simp only [length15,length16,Nat.reduceAdd]
  exact ⟨⟨checked15,checked16⟩,checked17⟩

theorem coverage : (dataT28Column2.blocks.toList.map Block.length).sum = 16384 := by
  simp only [dataT28Column2,raw_toList_append,List.map_append,List.sum_append,leafLength0,leafLength1,leafLength2,leafLength3,leafLength4,leafLength5,leafLength6,leafLength7,Nat.reduceAdd]

theorem checked : checkBlocks (fun n => n/128 ^^^ n%128) 0 dataT28Column2.blocks.toList = true := by
  simp only [dataT28Column2,raw_toList_append,checkBlocks_append_iff,List.map_append,List.sum_append,leafLength0,leafLength1,leafLength2,leafLength3,leafLength4,leafLength5,leafLength6,Nat.reduceAdd]
  exact ⟨⟨⟨leafChecked0,leafChecked1⟩,⟨leafChecked2,leafChecked3⟩⟩,⟨⟨leafChecked4,leafChecked5⟩,⟨leafChecked6,leafChecked7⟩⟩⟩

theorem output_get (i : Fin 16384) :
    dataT28.columns[2].get? i.val = some (i.val/128 ^^^ i.val%128) := by
  have result := checkBlocks_sound (fun n => n/128 ^^^ n%128) dataT28Column2.blocks.toList 0 i.val checked
    (by rw [coverage];exact i.isLt)
  change dataT28Column2.get? i.val = _
  simpa only [Column.get?,Nat.zero_add] using result

theorem output_value (i : Fin 16384) :
    ((dataT28.row i : Vector (ZMod mersenne31Modulus) 4)[2]).val = i.val/128 ^^^ i.val%128 := by
  have left : i.val/128 < 128 := by have := i.isLt;omega
  have right : i.val%128 < 128 := Nat.mod_lt _ (by decide)
  have bv : i.val/128 ^^^ i.val%128 =
      ((BitVec.ofNat 7 (i.val/128)) ^^^ (BitVec.ofNat 7 (i.val%128))).toNat := by
    simp [Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right]
  have small : i.val/128 ^^^ i.val%128 < 128 := by rw [bv];exact BitVec.isLt _
  have canonical : i.val/128 ^^^ i.val%128 < mersenne31Modulus := lt_trans small (by decide)
  simp only [TableData.row,TableData.rowNat,Vector.getElem_map,output_get,Option.getD_some]
  exact ZMod.val_natCast_of_lt canonical

end Airbender.Blake2Worker.Xor7Certificate
