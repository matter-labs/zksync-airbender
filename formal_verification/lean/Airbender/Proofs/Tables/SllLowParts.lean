import Airbender.Review.Helpers.Tables.NativeSllLowRows
import Airbender.Proofs.Tables.SllHigh
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Tables.LiteralSizes

namespace Airbender.Verification.SllLowProofs
open Setup Setup.Proofs NativeSllLow
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def highPrefix : List Block :=
  [.affine 98304 0 0,
   .affine 32768 1 0,
   .affine 16384 0 0,
   .affine 16384 1 0,
   .affine 16384 2 0,
   .affine 16384 3 0,
   .affine 8192 0 0,
   .affine 8192 1 0,
   .affine 8192 2 0,
   .affine 8192 3 0,
   .affine 8192 4 0,
   .affine 8192 5 0,
   .affine 8192 6 0,
   .affine 8192 7 0,
   .affine 4096 0 0,
   .affine 4096 1 0,
   .affine 4096 2 0,
   .affine 4096 3 0,
   .affine 4096 4 0,
   .affine 4096 5 0,
   .affine 4096 6 0,
   .affine 4096 7 0,
   .affine 4096 8 0,
   .affine 4096 9 0,
   .affine 4096 10 0,
   .affine 4096 11 0,
   .affine 4096 12 0,
   .affine 4096 13 0,
   .affine 4096 14 0,
   .affine 4096 15 0,
   .affine 2048 0 0,
   .affine 2048 1 0,
   .affine 2048 2 0,
   .affine 2048 3 0,
   .affine 2048 4 0,
   .affine 2048 5 0,
   .affine 2048 6 0,
   .affine 2048 7 0,
   .affine 2048 8 0,
   .affine 2048 9 0,
   .affine 2048 10 0,
   .affine 2048 11 0,
   .affine 2048 12 0,
   .affine 2048 13 0,
   .affine 2048 14 0,
   .affine 2048 15 0,
   .affine 2048 16 0,
   .affine 2048 17 0,
   .affine 2048 18 0,
   .affine 2048 19 0,
   .affine 2048 20 0,
   .affine 2048 21 0,
   .affine 2048 22 0,
   .affine 2048 23 0,
   .affine 2048 24 0,
   .affine 2048 25 0,
   .affine 2048 26 0,
   .affine 2048 27 0,
   .affine 2048 28 0,
   .affine 2048 29 0,
   .affine 2048 30 0,
   .affine 2048 31 0,
   .periodic 64 1 (Array.replicate 1024 0),
   .periodic 128 1 (Array.replicate 512 0),
   .periodic 256 1 (Array.replicate 256 0),
   .periodic 512 1 (Array.replicate 128 0),
   .periodic 1024 1 (Array.replicate 64 0),
   .periodic 2048 1 (Array.replicate 32 0),
   .periodic 4096 1 (Array.replicate 16 0),
   .periodic 8192 1 (Array.replicate 8 0),
   .periodic 16384 1 (Array.replicate 4 0),
   .periodic 32768 1 (Array.replicate 2 0)]

theorem native_high_shape : data.columns[2].blocks.toList =
    highPrefix ++ (SllHighProofs.part0 ++ SllHighProofs.part1 ++ SllHighProofs.part2 ++
      SllHighProofs.part3 ++ SllHighProofs.part4) := by
  rw [SllHighProofs.part0_shape,SllHighProofs.part1_shape,SllHighProofs.part2_shape,
    SllHighProofs.part3_shape,SllHighProofs.part4_shape]
  dsimp only [data,highPrefix,SllHighProofs.template6,SllHighProofs.template7,
    SllHighProofs.template8,SllHighProofs.template9,SllHighProofs.template10,
    SllHighProofs.template11,SllHighProofs.template12,SllHighProofs.template13,
    SllHighProofs.template14,SllHighProofs.template15,NativeSllHigh.data,
    Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_toList_append,List.cons_append,List.nil_append,raw_get_append,raw_literal_size,
    List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,
    Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
  rfl

def part0 : List Block := (highPrefix.drop 0).take 2

theorem part0_shape : part0 =
    [.affine 98304 0 0,
     .affine 32768 1 0] := rfl

theorem part0_extent : (part0.map Block.length).sum = 131072 := by
  rw [part0_shape]
  rfl

def part1 : List Block := (highPrefix.drop 2).take 4

theorem part1_shape : part1 =
    [.affine 16384 0 0,
     .affine 16384 1 0,
     .affine 16384 2 0,
     .affine 16384 3 0] := rfl

theorem part1_extent : (part1.map Block.length).sum = 65536 := by
  rw [part1_shape]
  rfl

def part2 : List Block := (highPrefix.drop 6).take 8

theorem part2_shape : part2 =
    [.affine 8192 0 0,
     .affine 8192 1 0,
     .affine 8192 2 0,
     .affine 8192 3 0,
     .affine 8192 4 0,
     .affine 8192 5 0,
     .affine 8192 6 0,
     .affine 8192 7 0] := rfl

theorem part2_extent : (part2.map Block.length).sum = 65536 := by
  rw [part2_shape]
  rfl

def part3 : List Block := (highPrefix.drop 14).take 16

theorem part3_shape : part3 =
    [.affine 4096 0 0,
     .affine 4096 1 0,
     .affine 4096 2 0,
     .affine 4096 3 0,
     .affine 4096 4 0,
     .affine 4096 5 0,
     .affine 4096 6 0,
     .affine 4096 7 0,
     .affine 4096 8 0,
     .affine 4096 9 0,
     .affine 4096 10 0,
     .affine 4096 11 0,
     .affine 4096 12 0,
     .affine 4096 13 0,
     .affine 4096 14 0,
     .affine 4096 15 0] := rfl

theorem part3_extent : (part3.map Block.length).sum = 65536 := by
  rw [part3_shape]
  rfl

def part4 : List Block := (highPrefix.drop 30).take 32

theorem part4_shape : part4 =
    [.affine 2048 0 0,
     .affine 2048 1 0,
     .affine 2048 2 0,
     .affine 2048 3 0,
     .affine 2048 4 0,
     .affine 2048 5 0,
     .affine 2048 6 0,
     .affine 2048 7 0,
     .affine 2048 8 0,
     .affine 2048 9 0,
     .affine 2048 10 0,
     .affine 2048 11 0,
     .affine 2048 12 0,
     .affine 2048 13 0,
     .affine 2048 14 0,
     .affine 2048 15 0,
     .affine 2048 16 0,
     .affine 2048 17 0,
     .affine 2048 18 0,
     .affine 2048 19 0,
     .affine 2048 20 0,
     .affine 2048 21 0,
     .affine 2048 22 0,
     .affine 2048 23 0,
     .affine 2048 24 0,
     .affine 2048 25 0,
     .affine 2048 26 0,
     .affine 2048 27 0,
     .affine 2048 28 0,
     .affine 2048 29 0,
     .affine 2048 30 0,
     .affine 2048 31 0] := rfl

theorem part4_extent : (part4.map Block.length).sum = 65536 := by
  rw [part4_shape]
  rfl

def part5 : List Block := (highPrefix.drop 62).take 10

theorem part5_shape : part5 =
    [.periodic 64 1 (Array.replicate 1024 0),
     .periodic 128 1 (Array.replicate 512 0),
     .periodic 256 1 (Array.replicate 256 0),
     .periodic 512 1 (Array.replicate 128 0),
     .periodic 1024 1 (Array.replicate 64 0),
     .periodic 2048 1 (Array.replicate 32 0),
     .periodic 4096 1 (Array.replicate 16 0),
     .periodic 8192 1 (Array.replicate 8 0),
     .periodic 16384 1 (Array.replicate 4 0),
     .periodic 32768 1 (Array.replicate 2 0)] := rfl

theorem part5_extent : (part5.map Block.length).sum = 655360 := by
  rw [part5_shape]
  rfl

theorem prefix_parts : highPrefix = part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 := rfl

theorem prefix_extent : (highPrefix.map Block.length).sum = 1048576 := by
  rw [prefix_parts]
  simp only [List.map_append,List.sum_append,part0_extent,part1_extent,part2_extent,
    part3_extent,part4_extent,part5_extent,Nat.reduceAdd]

end Airbender.Verification.SllLowProofs
