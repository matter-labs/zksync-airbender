import Airbender.Proofs.Tables.SllHighTemplate6
import Airbender.Proofs.Tables.SllHighTemplate7
import Airbender.Proofs.Tables.SllHighTemplate8
import Airbender.Proofs.Tables.SllHighTemplate9
import Airbender.Proofs.Tables.SllHighTemplate10
import Airbender.Proofs.Tables.SllHighTemplate11
import Airbender.Proofs.Tables.SllHighTemplate12
import Airbender.Proofs.Tables.SllHighTemplate13
import Airbender.Proofs.Tables.SllHighTemplate14
import Airbender.Proofs.Tables.SllHighTemplate15
import Airbender.Proofs.Tables.ImportedBlocks
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Tables.LiteralSizes
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.SllHighProofs
open Setup Setup.Proofs NativeSllHigh
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem native_blocks_shape : data.columns[2].blocks.toList =
    [.affine 65536 0 1,
     .affine 32768 0 2,
     .affine 32768 0 2,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
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
     .affine 2048 0 32,
     .periodic 64 0 template6,
     .periodic 128 0 template7,
     .periodic 256 0 template8,
     .periodic 512 0 template9,
     .periodic 1024 0 template10,
     .periodic 2048 0 template11,
     .periodic 4096 0 template12,
     .periodic 8192 0 template13,
     .periodic 16384 0 template14,
     .periodic 32768 0 template15,
     .affine 1048576 0 0] := by
  dsimp only [data,template6,template7,template8,template9,template10,template11,template12,template13,template14,template15,Vector.getElem_mk,Fin.getElem_fin,List.getElem_toArray,List.getElem_cons_zero,List.getElem_cons_succ]
  simp only [raw_toList_append,List.cons_append,List.nil_append,raw_get_append,raw_literal_size,List.getElem?_toArray,List.getElem?_cons_zero,List.getElem?_cons_succ,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,if_false]
  rfl

@[irreducible] noncomputable def part0 : List Block := (data.columns[2].blocks.toList.drop 0).take 7

theorem part0_shape : part0 =
    [.affine 65536 0 1,
     .affine 32768 0 2,
     .affine 32768 0 2,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4,
     .affine 16384 0 4] := by
  unfold part0
  conv_lhs => arg 2; rw [native_blocks_shape]
  rfl

theorem part0_extent : (part0.map Block.length).sum = 196608 := by
  rw [part0_shape]
  rfl

@[irreducible] noncomputable def part1 : List Block := (data.columns[2].blocks.toList.drop 7).take 8

theorem part1_shape : part1 =
    [.affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8,
     .affine 8192 0 8] := by
  unfold part1
  conv_lhs => arg 2; arg 2; rw [native_blocks_shape]
  rfl

theorem part1_extent : (part1.map Block.length).sum = 65536 := by
  rw [part1_shape]
  rfl

@[irreducible] noncomputable def part2 : List Block := (data.columns[2].blocks.toList.drop 15).take 16

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
     .affine 4096 0 16] := by
  unfold part2
  conv_lhs => arg 2; arg 2; rw [native_blocks_shape]
  rfl

theorem part2_extent : (part2.map Block.length).sum = 65536 := by
  rw [part2_shape]
  rfl

@[irreducible] noncomputable def part3 : List Block := (data.columns[2].blocks.toList.drop 31).take 32

theorem part3_shape : part3 =
    [.affine 2048 0 32,
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
     .affine 2048 0 32] := by
  unfold part3
  conv_lhs => arg 2; arg 2; rw [native_blocks_shape]
  rfl

theorem part3_extent : (part3.map Block.length).sum = 65536 := by
  rw [part3_shape]
  rfl

@[irreducible] noncomputable def part4 : List Block := (data.columns[2].blocks.toList.drop 63).take 10

theorem part4_shape : part4 =
    [.periodic 64 0 template6,
     .periodic 128 0 template7,
     .periodic 256 0 template8,
     .periodic 512 0 template9,
     .periodic 1024 0 template10,
     .periodic 2048 0 template11,
     .periodic 4096 0 template12,
     .periodic 8192 0 template13,
     .periodic 16384 0 template14,
     .periodic 32768 0 template15] := by
  unfold part4
  conv_lhs => arg 2; arg 2; rw [native_blocks_shape]
  rfl

private theorem periodic_extents (a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Array Nat)
    (h6 : a6.size = 1024)
    (h7 : a7.size = 512)
    (h8 : a8.size = 256)
    (h9 : a9.size = 128)
    (h10 : a10.size = 64)
    (h11 : a11.size = 32)
    (h12 : a12.size = 16)
    (h13 : a13.size = 8)
    (h14 : a14.size = 4)
    (h15 : a15.size = 2)
    : (([.periodic 64 0 a6, .periodic 128 0 a7, .periodic 256 0 a8, .periodic 512 0 a9, .periodic 1024 0 a10, .periodic 2048 0 a11, .periodic 4096 0 a12, .periodic 8192 0 a13, .periodic 16384 0 a14, .periodic 32768 0 a15] : List Block).map Block.length).sum = 655360 := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Block.length,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,Nat.reduceMul,Nat.reduceAdd]

theorem part4_extent : (part4.map Block.length).sum = 655360 := by
  exact (congrArg (fun blocks : List Block => (blocks.map Block.length).sum) part4_shape).trans
    (periodic_extents template6 template7 template8 template9 template10 template11 template12 template13 template14 template15
      template6_size template7_size template8_size template9_size template10_size template11_size template12_size template13_size template14_size template15_size)

@[irreducible] noncomputable def part5 : List Block := (data.columns[2].blocks.toList.drop 73).take 1

theorem part5_shape : part5 =
    [.affine 1048576 0 0] := by
  unfold part5
  conv_lhs => arg 2; arg 2; rw [native_blocks_shape]
  rfl

theorem part5_extent : (part5.map Block.length).sum = 1048576 := by
  rw [part5_shape]
  rfl

theorem parts : data.columns[2].blocks.toList =
    part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 := by
  have assembled := (congrArg₂ List.append (congrArg₂ List.append (congrArg₂ List.append (congrArg₂ List.append (congrArg₂ List.append part0_shape part1_shape) part2_shape) part3_shape) part4_shape) part5_shape)
  exact native_blocks_shape.trans assembled.symm

end Airbender.Verification.SllHighProofs
