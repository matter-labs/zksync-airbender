import Airbender.Proofs.Tables.SrlHighTemplate1
import Airbender.Proofs.Tables.SrlHighTemplate2
import Airbender.Proofs.Tables.SrlHighTemplate3
import Airbender.Proofs.Tables.SrlHighTemplate4
import Airbender.Proofs.Tables.SrlHighTemplate5
import Airbender.Proofs.Tables.SrlHighTemplate6
import Airbender.Proofs.Tables.SrlHighTemplate7
import Airbender.Proofs.Tables.SrlHighTemplate8
import Airbender.Proofs.Tables.SrlHighTemplate9
import Airbender.Proofs.Tables.SrlHighTemplate10
import Airbender.Proofs.Tables.SrlLow
import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Verification.SrlHighProofs
open Setup Setup.Proofs NativeSrlHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def lowPrefix : List Block :=
  [.affine 65537 0 0,
   .periodic 32768 0 template1,
   .periodic 16384 0 template2,
   .periodic 8192 0 template3,
   .periodic 4096 0 template4,
   .periodic 2048 0 template5,
   .periodic 1024 0 template6,
   .periodic 512 0 template7,
   .periodic 256 0 template8,
   .periodic 128 0 template9,
   .periodic 64 0 template10,
   .affine 2047 32 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 4096 0 16,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 8192 0 8,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 16384 0 4,
   .affine 32768 0 2,
   .affine 32768 0 2]

theorem native_low_shape : data.columns[1].blocks.toList =
    lowPrefix ++ (SrlLowProofs.part0 ++ SrlLowProofs.part1 ++ SrlLowProofs.part2 ++
      SrlLowProofs.part3 ++ SrlLowProofs.part4) := by
  rw [SrlLowProofs.part0_shape,SrlLowProofs.part1_shape,SrlLowProofs.part2_shape,
    SrlLowProofs.part3_shape,SrlLowProofs.part4_shape]
  dsimp only [data,lowPrefix,template1,template2,template3,template4,template5,template6,template7,template8,template9,template10, Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_toList_append,List.cons_append,List.nil_append,raw_get_append,raw_size_append,raw_literal_size,
    List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceLT,if_true]
  rfl

def part0 : List Block := (lowPrefix.drop 0).take 11

theorem part0_shape : part0 =
    [.affine 65537 0 0,
     .periodic 32768 0 template1,
     .periodic 16384 0 template2,
     .periodic 8192 0 template3,
     .periodic 4096 0 template4,
     .periodic 2048 0 template5,
     .periodic 1024 0 template6,
     .periodic 512 0 template7,
     .periodic 256 0 template8,
     .periodic 128 0 template9,
     .periodic 64 0 template10] := rfl

def part1 : List Block := (lowPrefix.drop 11).take 32

theorem part1_shape : part1 =
    [.affine 2047 32 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32,
     .affine 2048 0 32] := rfl

theorem part1_extent : (part1.map Block.length).sum = 65535 := by
  rw [part1_shape]
  rfl

def part2 : List Block := (lowPrefix.drop 43).take 16

theorem part2_shape : part2 =
    [.affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16,
     .affine 4096 0 16] := rfl

theorem part2_extent : (part2.map Block.length).sum = 65536 := by
  rw [part2_shape]
  rfl

def part3 : List Block := (lowPrefix.drop 59).take 8

theorem part3_shape : part3 =
    [.affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8] := rfl

theorem part3_extent : (part3.map Block.length).sum = 65536 := by
  rw [part3_shape]
  rfl

def part4 : List Block := (lowPrefix.drop 67).take 6

theorem part4_shape : part4 =
    [.affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 32768 0 2,
     .affine 32768 0 2] := rfl

theorem part4_extent : (part4.map Block.length).sum = 131072 := by
  rw [part4_shape]
  rfl

private theorem periodic_extents (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Array Nat)
    (size1 : a1.size = 2)
    (size2 : a2.size = 4)
    (size3 : a3.size = 8)
    (size4 : a4.size = 16)
    (size5 : a5.size = 32)
    (size6 : a6.size = 64)
    (size7 : a7.size = 128)
    (size8 : a8.size = 256)
    (size9 : a9.size = 512)
    (size10 : a10.size = 1024)
    : (([.affine 65537 0 0, .periodic 32768 0 a1, .periodic 16384 0 a2, .periodic 8192 0 a3, .periodic 4096 0 a4, .periodic 2048 0 a5, .periodic 1024 0 a6, .periodic 512 0 a7, .periodic 256 0 a8, .periodic 128 0 a9, .periodic 64 0 a10] : List Block).map Block.length).sum = 720897 := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Block.length,
    size1,size2,size3,size4,size5,size6,size7,size8,size9,size10,Nat.reduceMul,Nat.reduceAdd]

theorem part0_extent : (part0.map Block.length).sum = 720897 :=
  (congrArg (fun blocks => (blocks.map Block.length).sum) part0_shape).trans
    (periodic_extents template1 template2 template3 template4 template5 template6 template7 template8 template9 template10
      template1_size template2_size template3_size template4_size template5_size template6_size template7_size template8_size template9_size template10_size)

theorem prefix_parts : lowPrefix = part0 ++ part1 ++ part2 ++ part3 ++ part4 := rfl

theorem prefix_extent : (lowPrefix.map Block.length).sum = 1048576 := by
  rw [prefix_parts]
  simp only [List.map_append,List.sum_append,part0_extent,part1_extent,part2_extent,
    part3_extent,part4_extent,Nat.reduceAdd]

end Airbender.Verification.SrlHighProofs
