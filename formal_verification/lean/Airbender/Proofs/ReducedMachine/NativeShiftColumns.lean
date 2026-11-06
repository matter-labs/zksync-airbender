import Airbender.Proofs.ReducedMachine.NativeShiftBlocks1Part0
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks1Part1
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks1Part2
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks2Part0
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks2Part1
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks2Part2
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks2Part3
import Airbender.Proofs.ReducedMachine.NativeShiftBlocks2Part4
import Airbender.Proofs.ReducedMachine.NativeShiftReferences
import Airbender.Proofs.ReducedMachine.ShiftBlocks

namespace Airbender.ReducedMachine.NativeShiftColumnProofs
open Setup Setup.Proofs Verification NativeFixed ShiftBlockProofs NativeShiftShapeProofs
open NativeShiftReferenceProofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem column1_shape : dataT37.columns[1].blocks.toList =
    (column1Part0 ++ (column1Part1 ++ column1Part2)) := by
  calc
    _ = ([dataT37Column1Block0, dataT37Column1Block1, dataT37Column1Block2, dataT37Column1Block3, dataT37Column1Block4, dataT37Column1Block5, dataT37Column1Block6, dataT37Column1Block7, dataT37Column1Block8, dataT37Column1Block9, dataT37Column1Block10, dataT37Column1Block11, dataT37Column1Block12, dataT37Column1Block13, dataT37Column1Block14, dataT37Column1Block15, dataT37Column1Block16, dataT37Column1Block17, dataT37Column1Block18, dataT37Column1Block19, dataT37Column1Block20, dataT37Column1Block21, dataT37Column1Block22, dataT37Column1Block23, dataT37Column1Block24, dataT37Column1Block25, dataT37Column1Block26, dataT37Column1Block27, dataT37Column1Block28, dataT37Column1Block29, dataT37Column1Block30, dataT37Column1Block31, dataT37Column1Block32, dataT37Column1Block33, dataT37Column1Block34, dataT37Column1Block35, dataT37Column1Block36, dataT37Column1Block37, dataT37Column1Block38, dataT37Column1Block39, dataT37Column1Block40, dataT37Column1Block41, dataT37Column1Block42, dataT37Column1Block43, dataT37Column1Block44, dataT37Column1Block45, dataT37Column1Block46, dataT37Column1Block47, dataT37Column1Block48, dataT37Column1Block49, dataT37Column1Block50, dataT37Column1Block51, dataT37Column1Block52, dataT37Column1Block53, dataT37Column1Block54, dataT37Column1Block55, dataT37Column1Block56, dataT37Column1Block57, dataT37Column1Block58, dataT37Column1Block59, dataT37Column1Block60, dataT37Column1Block61, dataT37Column1Block62, dataT37Column1Block63] ++
      ([dataT37Column1Block64, dataT37Column1Block65, dataT37Column1Block66, dataT37Column1Block67, dataT37Column1Block68, dataT37Column1Block69, dataT37Column1Block70, dataT37Column1Block71, dataT37Column1Block72, dataT37Column1Block73, dataT37Column1Block74, dataT37Column1Block75, dataT37Column1Block76, dataT37Column1Block77, dataT37Column1Block78, dataT37Column1Block79, dataT37Column1Block80, dataT37Column1Block81, dataT37Column1Block82, dataT37Column1Block83, dataT37Column1Block84, dataT37Column1Block85, dataT37Column1Block86, dataT37Column1Block87, dataT37Column1Block88, dataT37Column1Block89, dataT37Column1Block90, dataT37Column1Block91, dataT37Column1Block92, dataT37Column1Block93, dataT37Column1Block94, dataT37Column1Block95, dataT37Column1Block96, dataT37Column1Block97, dataT37Column1Block98, dataT37Column1Block99, dataT37Column1Block100, dataT37Column1Block101, dataT37Column1Block102, dataT37Column1Block103, dataT37Column1Block104, dataT37Column1Block105, dataT37Column1Block106, dataT37Column1Block107, dataT37Column1Block108, dataT37Column1Block109, dataT37Column1Block110, dataT37Column1Block111, dataT37Column1Block112, dataT37Column1Block113, dataT37Column1Block114, dataT37Column1Block115, dataT37Column1Block116, dataT37Column1Block117, dataT37Column1Block118, dataT37Column1Block119, dataT37Column1Block120, dataT37Column1Block121, dataT37Column1Block122, dataT37Column1Block123, dataT37Column1Block124, dataT37Column1Block125, dataT37Column1Block126, dataT37Column1Block127] ++
      [dataT37Column1Block128, dataT37Column1Block129, dataT37Column1Block130, dataT37Column1Block131, dataT37Column1Block132, dataT37Column1Block133, dataT37Column1Block134, dataT37Column1Block135, dataT37Column1Block136, dataT37Column1Block137, dataT37Column1Block138, dataT37Column1Block139, dataT37Column1Block140, dataT37Column1Block141, dataT37Column1Block142, dataT37Column1Block143, dataT37Column1Block144, dataT37Column1Block145, dataT37Column1Block146, dataT37Column1Block147])) := by
      change dataT37Column1.blocks.toList = _
      simp only [dataT37Column1,raw_toList_append,List.cons_append,List.nil_append]
    _ = _ := (congrArg₂ List.append blocks1Part0 (congrArg₂ List.append blocks1Part1 blocks1Part2))

private def headBlocks : List Block :=
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
   .periodic 64 0 SllHighProofs.template6,
   .periodic 128 0 SllHighProofs.template7,
   .periodic 256 0 SllHighProofs.template8,
   .periodic 512 0 SllHighProofs.template9,
   .periodic 1024 0 SllHighProofs.template10,
   .periodic 2048 0 SllHighProofs.template11,
   .periodic 4096 0 SllHighProofs.template12,
   .periodic 8192 0 SllHighProofs.template13,
   .periodic 16384 0 SllHighProofs.template14,
   .periodic 32768 0 SllHighProofs.template15]

private def tailBlocks : List Block :=
  [.periodic 32768 1 (Array.replicate 2 0),
   .periodic 16384 1 (Array.replicate 4 0),
   .periodic 8192 1 (Array.replicate 8 0),
   .periodic 4096 1 (Array.replicate 16 0),
   .periodic 2048 1 (Array.replicate 32 0),
   .periodic 1024 1 (Array.replicate 64 0),
   .periodic 512 1 (Array.replicate 128 0),
   .periodic 256 1 (Array.replicate 256 0),
   .periodic 128 1 (Array.replicate 512 0),
   .periodic 64 1 (Array.replicate 1024 0),
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
   .affine 8192 0 0,
   .affine 8192 1 0,
   .affine 8192 2 0,
   .affine 8192 3 0,
   .affine 8192 4 0,
   .affine 8192 5 0,
   .affine 8192 6 0,
   .affine 8192 7 0,
   .affine 16384 0 0,
   .affine 16384 1 0,
   .affine 16384 2 0,
   .affine 16384 3 0,
   .affine 32768 0 0,
   .affine 32768 1 0,
   .affine 1048576 0 0]

private theorem canonical1 : (column1Part0 ++ (column1Part1 ++ column1Part2)) =
    headBlocks ++ (.affine 1048577 0 0 :: .affine 65535 1 1 :: tailBlocks) := by
  simp only [column1Part0,column1Part1,column1Part2,headBlocks,tailBlocks,
    List.cons_append,List.nil_append]

theorem column2_shape : dataT37.columns[2].blocks.toList =
    (column2Part0 ++ (column2Part1 ++ (column2Part2 ++ (column2Part3 ++ column2Part4)))) := by
  calc
    _ = ([dataT37Column2Block0, dataT37Column2Block1, dataT37Column2Block2, dataT37Column2Block3, dataT37Column2Block4, dataT37Column2Block5, dataT37Column2Block6, dataT37Column2Block7, dataT37Column2Block8, dataT37Column2Block9, dataT37Column2Block10, dataT37Column2Block11, dataT37Column2Block12, dataT37Column2Block13, dataT37Column2Block14, dataT37Column2Block15, dataT37Column2Block16, dataT37Column2Block17, dataT37Column2Block18, dataT37Column2Block19, dataT37Column2Block20, dataT37Column2Block21, dataT37Column2Block22, dataT37Column2Block23, dataT37Column2Block24, dataT37Column2Block25, dataT37Column2Block26, dataT37Column2Block27, dataT37Column2Block28, dataT37Column2Block29, dataT37Column2Block30, dataT37Column2Block31, dataT37Column2Block32, dataT37Column2Block33, dataT37Column2Block34, dataT37Column2Block35, dataT37Column2Block36, dataT37Column2Block37, dataT37Column2Block38, dataT37Column2Block39, dataT37Column2Block40, dataT37Column2Block41, dataT37Column2Block42, dataT37Column2Block43, dataT37Column2Block44, dataT37Column2Block45, dataT37Column2Block46, dataT37Column2Block47, dataT37Column2Block48, dataT37Column2Block49, dataT37Column2Block50, dataT37Column2Block51, dataT37Column2Block52, dataT37Column2Block53, dataT37Column2Block54, dataT37Column2Block55, dataT37Column2Block56, dataT37Column2Block57, dataT37Column2Block58, dataT37Column2Block59, dataT37Column2Block60, dataT37Column2Block61, dataT37Column2Block62, dataT37Column2Block63] ++
      ([dataT37Column2Block64, dataT37Column2Block65, dataT37Column2Block66, dataT37Column2Block67, dataT37Column2Block68, dataT37Column2Block69, dataT37Column2Block70, dataT37Column2Block71, dataT37Column2Block72, dataT37Column2Block73, dataT37Column2Block74, dataT37Column2Block75, dataT37Column2Block76, dataT37Column2Block77, dataT37Column2Block78, dataT37Column2Block79, dataT37Column2Block80, dataT37Column2Block81, dataT37Column2Block82, dataT37Column2Block83, dataT37Column2Block84, dataT37Column2Block85, dataT37Column2Block86, dataT37Column2Block87, dataT37Column2Block88, dataT37Column2Block89, dataT37Column2Block90, dataT37Column2Block91, dataT37Column2Block92, dataT37Column2Block93, dataT37Column2Block94, dataT37Column2Block95, dataT37Column2Block96, dataT37Column2Block97, dataT37Column2Block98, dataT37Column2Block99, dataT37Column2Block100, dataT37Column2Block101, dataT37Column2Block102, dataT37Column2Block103, dataT37Column2Block104, dataT37Column2Block105, dataT37Column2Block106, dataT37Column2Block107, dataT37Column2Block108, dataT37Column2Block109, dataT37Column2Block110, dataT37Column2Block111, dataT37Column2Block112, dataT37Column2Block113, dataT37Column2Block114, dataT37Column2Block115, dataT37Column2Block116, dataT37Column2Block117, dataT37Column2Block118, dataT37Column2Block119, dataT37Column2Block120, dataT37Column2Block121, dataT37Column2Block122, dataT37Column2Block123, dataT37Column2Block124, dataT37Column2Block125, dataT37Column2Block126, dataT37Column2Block127] ++
      ([dataT37Column2Block128, dataT37Column2Block129, dataT37Column2Block130, dataT37Column2Block131, dataT37Column2Block132, dataT37Column2Block133, dataT37Column2Block134, dataT37Column2Block135, dataT37Column2Block136, dataT37Column2Block137, dataT37Column2Block138, dataT37Column2Block139, dataT37Column2Block140, dataT37Column2Block141, dataT37Column2Block142, dataT37Column2Block143, dataT37Column2Block144, dataT37Column2Block145, dataT37Column2Block146, dataT37Column2Block147, dataT37Column2Block148, dataT37Column2Block149, dataT37Column2Block150, dataT37Column2Block151, dataT37Column2Block152, dataT37Column2Block153, dataT37Column2Block154, dataT37Column2Block155, dataT37Column2Block156, dataT37Column2Block157, dataT37Column2Block158, dataT37Column2Block159, dataT37Column2Block160, dataT37Column2Block161, dataT37Column2Block162, dataT37Column2Block163, dataT37Column2Block164, dataT37Column2Block165, dataT37Column2Block166, dataT37Column2Block167, dataT37Column2Block168, dataT37Column2Block169, dataT37Column2Block170, dataT37Column2Block171, dataT37Column2Block172, dataT37Column2Block173, dataT37Column2Block174, dataT37Column2Block175, dataT37Column2Block176, dataT37Column2Block177, dataT37Column2Block178, dataT37Column2Block179, dataT37Column2Block180, dataT37Column2Block181, dataT37Column2Block182, dataT37Column2Block183, dataT37Column2Block184, dataT37Column2Block185, dataT37Column2Block186, dataT37Column2Block187, dataT37Column2Block188, dataT37Column2Block189, dataT37Column2Block190, dataT37Column2Block191] ++
      ([dataT37Column2Block192, dataT37Column2Block193, dataT37Column2Block194, dataT37Column2Block195, dataT37Column2Block196, dataT37Column2Block197, dataT37Column2Block198, dataT37Column2Block199, dataT37Column2Block200, dataT37Column2Block201, dataT37Column2Block202, dataT37Column2Block203, dataT37Column2Block204, dataT37Column2Block205, dataT37Column2Block206, dataT37Column2Block207, dataT37Column2Block208, dataT37Column2Block209, dataT37Column2Block210, dataT37Column2Block211, dataT37Column2Block212, dataT37Column2Block213, dataT37Column2Block214, dataT37Column2Block215, dataT37Column2Block216, dataT37Column2Block217, dataT37Column2Block218, dataT37Column2Block219, dataT37Column2Block220, dataT37Column2Block221, dataT37Column2Block222, dataT37Column2Block223, dataT37Column2Block224, dataT37Column2Block225, dataT37Column2Block226, dataT37Column2Block227, dataT37Column2Block228, dataT37Column2Block229, dataT37Column2Block230, dataT37Column2Block231, dataT37Column2Block232, dataT37Column2Block233, dataT37Column2Block234, dataT37Column2Block235, dataT37Column2Block236, dataT37Column2Block237, dataT37Column2Block238, dataT37Column2Block239, dataT37Column2Block240, dataT37Column2Block241, dataT37Column2Block242, dataT37Column2Block243, dataT37Column2Block244, dataT37Column2Block245, dataT37Column2Block246, dataT37Column2Block247, dataT37Column2Block248, dataT37Column2Block249, dataT37Column2Block250, dataT37Column2Block251, dataT37Column2Block252, dataT37Column2Block253, dataT37Column2Block254, dataT37Column2Block255] ++
      [dataT37Column2Block256, dataT37Column2Block257, dataT37Column2Block258, dataT37Column2Block259, dataT37Column2Block260, dataT37Column2Block261, dataT37Column2Block262, dataT37Column2Block263, dataT37Column2Block264, dataT37Column2Block265, dataT37Column2Block266, dataT37Column2Block267, dataT37Column2Block268, dataT37Column2Block269, dataT37Column2Block270, dataT37Column2Block271, dataT37Column2Block272, dataT37Column2Block273, dataT37Column2Block274, dataT37Column2Block275, dataT37Column2Block276, dataT37Column2Block277, dataT37Column2Block278, dataT37Column2Block279, dataT37Column2Block280, dataT37Column2Block281, dataT37Column2Block282, dataT37Column2Block283, dataT37Column2Block284, dataT37Column2Block285, dataT37Column2Block286, dataT37Column2Block287, dataT37Column2Block288, dataT37Column2Block289, dataT37Column2Block290])))) := by
      change dataT37Column2.blocks.toList = _
      simp only [dataT37Column2,raw_toList_append,List.cons_append,List.nil_append]
    _ = _ := (congrArg₂ List.append blocks2Part0 (congrArg₂ List.append blocks2Part1 (congrArg₂ List.append blocks2Part2 (congrArg₂ List.append blocks2Part3 blocks2Part4))))

private def leftRemaining : List Block :=
  [.affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .affine 2048 0 32,
   .periodic 64 0 SllHighProofs.template6,
   .periodic 128 0 SllHighProofs.template7,
   .periodic 256 0 SllHighProofs.template8,
   .periodic 512 0 SllHighProofs.template9,
   .periodic 1024 0 SllHighProofs.template10,
   .periodic 2048 0 SllHighProofs.template11,
   .periodic 4096 0 SllHighProofs.template12,
   .periodic 8192 0 SllHighProofs.template13,
   .periodic 16384 0 SllHighProofs.template14,
   .periodic 32768 0 SllHighProofs.template15]

private def rightFirst : List Block :=
  [.affine 65537 0 0,
   .periodic 32768 0 SrlHighProofs.template1,
   .periodic 16384 0 SrlHighProofs.template2,
   .periodic 8192 0 SrlHighProofs.template3,
   .periodic 4096 0 SrlHighProofs.template4,
   .periodic 2048 0 SrlHighProofs.template5,
   .periodic 1024 0 SrlHighProofs.template6,
   .periodic 512 0 SrlHighProofs.template7,
   .periodic 256 0 SrlHighProofs.template8,
   .periodic 128 0 SrlHighProofs.template9,
   .periodic 64 0 SrlHighProofs.template10,
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
   .affine 4096 0 16]

private theorem left_partition : leftHigh =
    column2Part0 ++ (column2Part1 ++ leftRemaining) := by
  simp only [leftHigh,column2Part0,column2Part1,leftRemaining,List.cons_append,List.nil_append]
private theorem right_partition : rightLow =
    rightFirst ++ (column2Part3 ++ column2Part4) := by
  simp only [rightLow,rightFirst,column2Part3,column2Part4,List.cons_append,List.nil_append]
private theorem middle_partition : column2Part2 = leftRemaining ++ rightFirst := by
  simp only [column2Part2,leftRemaining,rightFirst,List.cons_append,List.nil_append]

private theorem canonical2 :
    column2Part0 ++ (column2Part1 ++ (column2Part2 ++ (column2Part3 ++ column2Part4))) =
      leftHigh ++ rightLow := by
  rw [left_partition,right_partition,middle_partition]
  simp only [List.append_assoc]

private theorem left_split : leftLow = headBlocks ++ [.affine 1048576 0 0] := rfl
private theorem right_split : rightHigh = .affine 65536 0 1 :: tailBlocks := rfl

/-- Exact getter equality across the native zero/ascending compression boundary. -/
theorem first_reads (n : Nat) : dataT37.columns[1].get? n =
    getFromBlocks (NativeSllLow.data.columns[1].blocks.toList ++
      NativeSrlHigh.data.columns[2].blocks.toList) n := by
  rw [Column.get?,column1_shape,canonical1,left_low_shape,right_high_shape,
    left_split,right_split,List.append_assoc]
  rw [get_append headBlocks,get_append headBlocks]
  split
  · rfl
  · exact native_boundary 1048576 65536 (by decide) tailBlocks _

/-- The other output column appends exact already-certified block streams. -/
theorem second_reads (n : Nat) : dataT37.columns[2].get? n =
    getFromBlocks (NativeSllLow.data.columns[2].blocks.toList ++
      NativeSrlHigh.data.columns[1].blocks.toList) n := by
  rw [Column.get?,column2_shape,canonical2,left_high_shape,right_low_shape]

private theorem low_extent :
    (NativeSllLow.data.columns[1].blocks.toList.map Block.length).sum = 2097152 := by
  rw [SllLowProofs.native_low_column]
  exact SllHighProofs.native_output_extent

/-- Native right-shift outputs are reversed relative to the earlier split table. -/
theorem output (lane : Fin 2) (i : Fin 4194304) :
    dataT37.columns[1 + lane.val].get? i.val =
      if i.val < 2097152 then NativeSllLow.data.columns[1 + lane.val].get? i.val
      else NativeSrlHigh.data.columns[2 - lane.val].get? (i.val - 2097152) := by
  fin_cases lane
  · change dataT37.columns[1].get? i.val = _
    rw [first_reads,get_append,low_extent]
    rfl
  · change dataT37.columns[2].get? i.val = _
    rw [second_reads,get_append,SllLowProofs.native_high_extent]
    rfl

end Airbender.ReducedMachine.NativeShiftColumnProofs
