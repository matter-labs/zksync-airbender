import Airbender.Proofs.Blake2G.Xor9PackedCertificate

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

theorem extent0 :
    (xor9ColumnBlocks0.toList.map Block.length).sum = xor9ColumnSize0 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    0 (⟨xor9ColumnStart0, Xor9PackedCapture.blocks0, xor9ColumnSize0⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding0] at result
  exact result

theorem output_part0 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart0
      xor9ColumnBlocks0.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    0 (⟨xor9ColumnStart0, Xor9PackedCapture.blocks0, xor9ColumnSize0⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding0] at result
  exact result

theorem extent1 :
    (xor9ColumnBlocks1.toList.map Block.length).sum = xor9ColumnSize1 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    1 (⟨xor9ColumnStart1, Xor9PackedCapture.blocks1, xor9ColumnSize1⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding1] at result
  exact result

theorem output_part1 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart1
      xor9ColumnBlocks1.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    1 (⟨xor9ColumnStart1, Xor9PackedCapture.blocks1, xor9ColumnSize1⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding1] at result
  exact result

theorem extent2 :
    (xor9ColumnBlocks2.toList.map Block.length).sum = xor9ColumnSize2 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    2 (⟨xor9ColumnStart2, Xor9PackedCapture.blocks2, xor9ColumnSize2⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding2] at result
  exact result

theorem output_part2 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart2
      xor9ColumnBlocks2.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    2 (⟨xor9ColumnStart2, Xor9PackedCapture.blocks2, xor9ColumnSize2⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding2] at result
  exact result

theorem extent3 :
    (xor9ColumnBlocks3.toList.map Block.length).sum = xor9ColumnSize3 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    3 (⟨xor9ColumnStart3, Xor9PackedCapture.blocks3, xor9ColumnSize3⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding3] at result
  exact result

theorem output_part3 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart3
      xor9ColumnBlocks3.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    3 (⟨xor9ColumnStart3, Xor9PackedCapture.blocks3, xor9ColumnSize3⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding3] at result
  exact result

theorem extent4 :
    (xor9ColumnBlocks4.toList.map Block.length).sum = xor9ColumnSize4 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    4 (⟨xor9ColumnStart4, Xor9PackedCapture.blocks4, xor9ColumnSize4⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding4] at result
  exact result

theorem output_part4 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart4
      xor9ColumnBlocks4.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    4 (⟨xor9ColumnStart4, Xor9PackedCapture.blocks4, xor9ColumnSize4⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding4] at result
  exact result

theorem extent5 :
    (xor9ColumnBlocks5.toList.map Block.length).sum = xor9ColumnSize5 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    5 (⟨xor9ColumnStart5, Xor9PackedCapture.blocks5, xor9ColumnSize5⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding5] at result
  exact result

theorem output_part5 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart5
      xor9ColumnBlocks5.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    5 (⟨xor9ColumnStart5, Xor9PackedCapture.blocks5, xor9ColumnSize5⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding5] at result
  exact result

theorem extent6 :
    (xor9ColumnBlocks6.toList.map Block.length).sum = xor9ColumnSize6 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    6 (⟨xor9ColumnStart6, Xor9PackedCapture.blocks6, xor9ColumnSize6⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding6] at result
  exact result

theorem output_part6 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart6
      xor9ColumnBlocks6.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    6 (⟨xor9ColumnStart6, Xor9PackedCapture.blocks6, xor9ColumnSize6⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding6] at result
  exact result

theorem extent7 :
    (xor9ColumnBlocks7.toList.map Block.length).sum = xor9ColumnSize7 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    7 (⟨xor9ColumnStart7, Xor9PackedCapture.blocks7, xor9ColumnSize7⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding7] at result
  exact result

theorem output_part7 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart7
      xor9ColumnBlocks7.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    7 (⟨xor9ColumnStart7, Xor9PackedCapture.blocks7, xor9ColumnSize7⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding7] at result
  exact result

theorem extent8 :
    (xor9ColumnBlocks8.toList.map Block.length).sum = xor9ColumnSize8 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    8 (⟨xor9ColumnStart8, Xor9PackedCapture.blocks8, xor9ColumnSize8⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding8] at result
  exact result

theorem output_part8 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart8
      xor9ColumnBlocks8.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    8 (⟨xor9ColumnStart8, Xor9PackedCapture.blocks8, xor9ColumnSize8⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding8] at result
  exact result

theorem extent9 :
    (xor9ColumnBlocks9.toList.map Block.length).sum = xor9ColumnSize9 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    9 (⟨xor9ColumnStart9, Xor9PackedCapture.blocks9, xor9ColumnSize9⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding9] at result
  exact result

theorem output_part9 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart9
      xor9ColumnBlocks9.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    9 (⟨xor9ColumnStart9, Xor9PackedCapture.blocks9, xor9ColumnSize9⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding9] at result
  exact result

theorem extent10 :
    (xor9ColumnBlocks10.toList.map Block.length).sum = xor9ColumnSize10 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    10 (⟨xor9ColumnStart10, Xor9PackedCapture.blocks10, xor9ColumnSize10⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding10] at result
  exact result

theorem output_part10 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart10
      xor9ColumnBlocks10.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    10 (⟨xor9ColumnStart10, Xor9PackedCapture.blocks10, xor9ColumnSize10⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding10] at result
  exact result

theorem extent11 :
    (xor9ColumnBlocks11.toList.map Block.length).sum = xor9ColumnSize11 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    11 (⟨xor9ColumnStart11, Xor9PackedCapture.blocks11, xor9ColumnSize11⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding11] at result
  exact result

theorem output_part11 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart11
      xor9ColumnBlocks11.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    11 (⟨xor9ColumnStart11, Xor9PackedCapture.blocks11, xor9ColumnSize11⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding11] at result
  exact result

theorem extent12 :
    (xor9ColumnBlocks12.toList.map Block.length).sum = xor9ColumnSize12 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    12 (⟨xor9ColumnStart12, Xor9PackedCapture.blocks12, xor9ColumnSize12⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding12] at result
  exact result

theorem output_part12 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart12
      xor9ColumnBlocks12.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    12 (⟨xor9ColumnStart12, Xor9PackedCapture.blocks12, xor9ColumnSize12⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding12] at result
  exact result

theorem extent13 :
    (xor9ColumnBlocks13.toList.map Block.length).sum = xor9ColumnSize13 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    13 (⟨xor9ColumnStart13, Xor9PackedCapture.blocks13, xor9ColumnSize13⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding13] at result
  exact result

theorem output_part13 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart13
      xor9ColumnBlocks13.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    13 (⟨xor9ColumnStart13, Xor9PackedCapture.blocks13, xor9ColumnSize13⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding13] at result
  exact result

theorem extent14 :
    (xor9ColumnBlocks14.toList.map Block.length).sum = xor9ColumnSize14 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    14 (⟨xor9ColumnStart14, Xor9PackedCapture.blocks14, xor9ColumnSize14⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding14] at result
  exact result

theorem output_part14 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart14
      xor9ColumnBlocks14.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    14 (⟨xor9ColumnStart14, Xor9PackedCapture.blocks14, xor9ColumnSize14⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding14] at result
  exact result

theorem extent15 :
    (xor9ColumnBlocks15.toList.map Block.length).sum = xor9ColumnSize15 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    15 (⟨xor9ColumnStart15, Xor9PackedCapture.blocks15, xor9ColumnSize15⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding15] at result
  exact result

theorem output_part15 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart15
      xor9ColumnBlocks15.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    15 (⟨xor9ColumnStart15, Xor9PackedCapture.blocks15, xor9ColumnSize15⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding15] at result
  exact result

theorem extent16 :
    (xor9ColumnBlocks16.toList.map Block.length).sum = xor9ColumnSize16 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    16 (⟨xor9ColumnStart16, Xor9PackedCapture.blocks16, xor9ColumnSize16⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding16] at result
  exact result

theorem output_part16 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart16
      xor9ColumnBlocks16.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    16 (⟨xor9ColumnStart16, Xor9PackedCapture.blocks16, xor9ColumnSize16⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding16] at result
  exact result

theorem extent17 :
    (xor9ColumnBlocks17.toList.map Block.length).sum = xor9ColumnSize17 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    17 (⟨xor9ColumnStart17, Xor9PackedCapture.blocks17, xor9ColumnSize17⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding17] at result
  exact result

theorem output_part17 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart17
      xor9ColumnBlocks17.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    17 (⟨xor9ColumnStart17, Xor9PackedCapture.blocks17, xor9ColumnSize17⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding17] at result
  exact result

theorem extent18 :
    (xor9ColumnBlocks18.toList.map Block.length).sum = xor9ColumnSize18 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    18 (⟨xor9ColumnStart18, Xor9PackedCapture.blocks18, xor9ColumnSize18⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding18] at result
  exact result

theorem output_part18 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart18
      xor9ColumnBlocks18.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    18 (⟨xor9ColumnStart18, Xor9PackedCapture.blocks18, xor9ColumnSize18⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding18] at result
  exact result

theorem extent19 :
    (xor9ColumnBlocks19.toList.map Block.length).sum = xor9ColumnSize19 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    19 (⟨xor9ColumnStart19, Xor9PackedCapture.blocks19, xor9ColumnSize19⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding19] at result
  exact result

theorem output_part19 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart19
      xor9ColumnBlocks19.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    19 (⟨xor9ColumnStart19, Xor9PackedCapture.blocks19, xor9ColumnSize19⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding19] at result
  exact result

theorem extent20 :
    (xor9ColumnBlocks20.toList.map Block.length).sum = xor9ColumnSize20 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    20 (⟨xor9ColumnStart20, Xor9PackedCapture.blocks20, xor9ColumnSize20⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding20] at result
  exact result

theorem output_part20 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart20
      xor9ColumnBlocks20.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    20 (⟨xor9ColumnStart20, Xor9PackedCapture.blocks20, xor9ColumnSize20⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding20] at result
  exact result

theorem extent21 :
    (xor9ColumnBlocks21.toList.map Block.length).sum = xor9ColumnSize21 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    21 (⟨xor9ColumnStart21, Xor9PackedCapture.blocks21, xor9ColumnSize21⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding21] at result
  exact result

theorem output_part21 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart21
      xor9ColumnBlocks21.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    21 (⟨xor9ColumnStart21, Xor9PackedCapture.blocks21, xor9ColumnSize21⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding21] at result
  exact result

theorem extent22 :
    (xor9ColumnBlocks22.toList.map Block.length).sum = xor9ColumnSize22 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    22 (⟨xor9ColumnStart22, Xor9PackedCapture.blocks22, xor9ColumnSize22⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding22] at result
  exact result

theorem output_part22 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart22
      xor9ColumnBlocks22.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    22 (⟨xor9ColumnStart22, Xor9PackedCapture.blocks22, xor9ColumnSize22⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding22] at result
  exact result

theorem extent23 :
    (xor9ColumnBlocks23.toList.map Block.length).sum = xor9ColumnSize23 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    23 (⟨xor9ColumnStart23, Xor9PackedCapture.blocks23, xor9ColumnSize23⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding23] at result
  exact result

theorem output_part23 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart23
      xor9ColumnBlocks23.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    23 (⟨xor9ColumnStart23, Xor9PackedCapture.blocks23, xor9ColumnSize23⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding23] at result
  exact result

theorem extent24 :
    (xor9ColumnBlocks24.toList.map Block.length).sum = xor9ColumnSize24 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    24 (⟨xor9ColumnStart24, Xor9PackedCapture.blocks24, xor9ColumnSize24⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding24] at result
  exact result

theorem output_part24 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart24
      xor9ColumnBlocks24.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    24 (⟨xor9ColumnStart24, Xor9PackedCapture.blocks24, xor9ColumnSize24⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding24] at result
  exact result

theorem extent25 :
    (xor9ColumnBlocks25.toList.map Block.length).sum = xor9ColumnSize25 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    25 (⟨xor9ColumnStart25, Xor9PackedCapture.blocks25, xor9ColumnSize25⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding25] at result
  exact result

theorem output_part25 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart25
      xor9ColumnBlocks25.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    25 (⟨xor9ColumnStart25, Xor9PackedCapture.blocks25, xor9ColumnSize25⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding25] at result
  exact result

theorem extent26 :
    (xor9ColumnBlocks26.toList.map Block.length).sum = xor9ColumnSize26 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    26 (⟨xor9ColumnStart26, Xor9PackedCapture.blocks26, xor9ColumnSize26⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding26] at result
  exact result

theorem output_part26 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart26
      xor9ColumnBlocks26.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    26 (⟨xor9ColumnStart26, Xor9PackedCapture.blocks26, xor9ColumnSize26⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding26] at result
  exact result

theorem extent27 :
    (xor9ColumnBlocks27.toList.map Block.length).sum = xor9ColumnSize27 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    27 (⟨xor9ColumnStart27, Xor9PackedCapture.blocks27, xor9ColumnSize27⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding27] at result
  exact result

theorem output_part27 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart27
      xor9ColumnBlocks27.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    27 (⟨xor9ColumnStart27, Xor9PackedCapture.blocks27, xor9ColumnSize27⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding27] at result
  exact result

theorem extent28 :
    (xor9ColumnBlocks28.toList.map Block.length).sum = xor9ColumnSize28 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    28 (⟨xor9ColumnStart28, Xor9PackedCapture.blocks28, xor9ColumnSize28⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding28] at result
  exact result

theorem output_part28 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart28
      xor9ColumnBlocks28.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    28 (⟨xor9ColumnStart28, Xor9PackedCapture.blocks28, xor9ColumnSize28⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding28] at result
  exact result

theorem extent29 :
    (xor9ColumnBlocks29.toList.map Block.length).sum = xor9ColumnSize29 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    29 (⟨xor9ColumnStart29, Xor9PackedCapture.blocks29, xor9ColumnSize29⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding29] at result
  exact result

theorem output_part29 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart29
      xor9ColumnBlocks29.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    29 (⟨xor9ColumnStart29, Xor9PackedCapture.blocks29, xor9ColumnSize29⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding29] at result
  exact result

theorem extent30 :
    (xor9ColumnBlocks30.toList.map Block.length).sum = xor9ColumnSize30 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    30 (⟨xor9ColumnStart30, Xor9PackedCapture.blocks30, xor9ColumnSize30⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding30] at result
  exact result

theorem output_part30 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart30
      xor9ColumnBlocks30.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    30 (⟨xor9ColumnStart30, Xor9PackedCapture.blocks30, xor9ColumnSize30⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding30] at result
  exact result

theorem extent31 :
    (xor9ColumnBlocks31.toList.map Block.length).sum = xor9ColumnSize31 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    31 (⟨xor9ColumnStart31, Xor9PackedCapture.blocks31, xor9ColumnSize31⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding31] at result
  exact result

theorem output_part31 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart31
      xor9ColumnBlocks31.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    31 (⟨xor9ColumnStart31, Xor9PackedCapture.blocks31, xor9ColumnSize31⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding31] at result
  exact result

theorem extent32 :
    (xor9ColumnBlocks32.toList.map Block.length).sum = xor9ColumnSize32 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    32 (⟨xor9ColumnStart32, Xor9PackedCapture.blocks32, xor9ColumnSize32⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding32] at result
  exact result

theorem output_part32 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart32
      xor9ColumnBlocks32.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    32 (⟨xor9ColumnStart32, Xor9PackedCapture.blocks32, xor9ColumnSize32⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding32] at result
  exact result

theorem extent33 :
    (xor9ColumnBlocks33.toList.map Block.length).sum = xor9ColumnSize33 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    33 (⟨xor9ColumnStart33, Xor9PackedCapture.blocks33, xor9ColumnSize33⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding33] at result
  exact result

theorem output_part33 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart33
      xor9ColumnBlocks33.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    33 (⟨xor9ColumnStart33, Xor9PackedCapture.blocks33, xor9ColumnSize33⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding33] at result
  exact result

theorem extent34 :
    (xor9ColumnBlocks34.toList.map Block.length).sum = xor9ColumnSize34 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    34 (⟨xor9ColumnStart34, Xor9PackedCapture.blocks34, xor9ColumnSize34⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding34] at result
  exact result

theorem output_part34 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart34
      xor9ColumnBlocks34.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    34 (⟨xor9ColumnStart34, Xor9PackedCapture.blocks34, xor9ColumnSize34⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding34] at result
  exact result

theorem extent35 :
    (xor9ColumnBlocks35.toList.map Block.length).sum = xor9ColumnSize35 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    35 (⟨xor9ColumnStart35, Xor9PackedCapture.blocks35, xor9ColumnSize35⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding35] at result
  exact result

theorem output_part35 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart35
      xor9ColumnBlocks35.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    35 (⟨xor9ColumnStart35, Xor9PackedCapture.blocks35, xor9ColumnSize35⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding35] at result
  exact result

theorem extent36 :
    (xor9ColumnBlocks36.toList.map Block.length).sum = xor9ColumnSize36 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    36 (⟨xor9ColumnStart36, Xor9PackedCapture.blocks36, xor9ColumnSize36⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding36] at result
  exact result

theorem output_part36 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart36
      xor9ColumnBlocks36.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    36 (⟨xor9ColumnStart36, Xor9PackedCapture.blocks36, xor9ColumnSize36⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding36] at result
  exact result

theorem extent37 :
    (xor9ColumnBlocks37.toList.map Block.length).sum = xor9ColumnSize37 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    37 (⟨xor9ColumnStart37, Xor9PackedCapture.blocks37, xor9ColumnSize37⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding37] at result
  exact result

theorem output_part37 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart37
      xor9ColumnBlocks37.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    37 (⟨xor9ColumnStart37, Xor9PackedCapture.blocks37, xor9ColumnSize37⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding37] at result
  exact result

theorem extent38 :
    (xor9ColumnBlocks38.toList.map Block.length).sum = xor9ColumnSize38 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    38 (⟨xor9ColumnStart38, Xor9PackedCapture.blocks38, xor9ColumnSize38⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding38] at result
  exact result

theorem output_part38 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart38
      xor9ColumnBlocks38.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    38 (⟨xor9ColumnStart38, Xor9PackedCapture.blocks38, xor9ColumnSize38⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding38] at result
  exact result

theorem extent39 :
    (xor9ColumnBlocks39.toList.map Block.length).sum = xor9ColumnSize39 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    39 (⟨xor9ColumnStart39, Xor9PackedCapture.blocks39, xor9ColumnSize39⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding39] at result
  exact result

theorem output_part39 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart39
      xor9ColumnBlocks39.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    39 (⟨xor9ColumnStart39, Xor9PackedCapture.blocks39, xor9ColumnSize39⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding39] at result
  exact result

theorem extent40 :
    (xor9ColumnBlocks40.toList.map Block.length).sum = xor9ColumnSize40 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    40 (⟨xor9ColumnStart40, Xor9PackedCapture.blocks40, xor9ColumnSize40⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding40] at result
  exact result

theorem output_part40 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart40
      xor9ColumnBlocks40.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    40 (⟨xor9ColumnStart40, Xor9PackedCapture.blocks40, xor9ColumnSize40⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding40] at result
  exact result

theorem extent41 :
    (xor9ColumnBlocks41.toList.map Block.length).sum = xor9ColumnSize41 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    41 (⟨xor9ColumnStart41, Xor9PackedCapture.blocks41, xor9ColumnSize41⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding41] at result
  exact result

theorem output_part41 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart41
      xor9ColumnBlocks41.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    41 (⟨xor9ColumnStart41, Xor9PackedCapture.blocks41, xor9ColumnSize41⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding41] at result
  exact result

theorem extent42 :
    (xor9ColumnBlocks42.toList.map Block.length).sum = xor9ColumnSize42 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    42 (⟨xor9ColumnStart42, Xor9PackedCapture.blocks42, xor9ColumnSize42⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding42] at result
  exact result

theorem output_part42 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart42
      xor9ColumnBlocks42.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    42 (⟨xor9ColumnStart42, Xor9PackedCapture.blocks42, xor9ColumnSize42⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding42] at result
  exact result

theorem extent43 :
    (xor9ColumnBlocks43.toList.map Block.length).sum = xor9ColumnSize43 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    43 (⟨xor9ColumnStart43, Xor9PackedCapture.blocks43, xor9ColumnSize43⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding43] at result
  exact result

theorem output_part43 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart43
      xor9ColumnBlocks43.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    43 (⟨xor9ColumnStart43, Xor9PackedCapture.blocks43, xor9ColumnSize43⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding43] at result
  exact result

theorem extent44 :
    (xor9ColumnBlocks44.toList.map Block.length).sum = xor9ColumnSize44 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    44 (⟨xor9ColumnStart44, Xor9PackedCapture.blocks44, xor9ColumnSize44⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding44] at result
  exact result

theorem output_part44 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart44
      xor9ColumnBlocks44.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    44 (⟨xor9ColumnStart44, Xor9PackedCapture.blocks44, xor9ColumnSize44⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding44] at result
  exact result

theorem extent45 :
    (xor9ColumnBlocks45.toList.map Block.length).sum = xor9ColumnSize45 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    45 (⟨xor9ColumnStart45, Xor9PackedCapture.blocks45, xor9ColumnSize45⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding45] at result
  exact result

theorem output_part45 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart45
      xor9ColumnBlocks45.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    45 (⟨xor9ColumnStart45, Xor9PackedCapture.blocks45, xor9ColumnSize45⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding45] at result
  exact result

theorem extent46 :
    (xor9ColumnBlocks46.toList.map Block.length).sum = xor9ColumnSize46 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    46 (⟨xor9ColumnStart46, Xor9PackedCapture.blocks46, xor9ColumnSize46⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding46] at result
  exact result

theorem output_part46 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart46
      xor9ColumnBlocks46.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    46 (⟨xor9ColumnStart46, Xor9PackedCapture.blocks46, xor9ColumnSize46⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding46] at result
  exact result

theorem extent47 :
    (xor9ColumnBlocks47.toList.map Block.length).sum = xor9ColumnSize47 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    47 (⟨xor9ColumnStart47, Xor9PackedCapture.blocks47, xor9ColumnSize47⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding47] at result
  exact result

theorem output_part47 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart47
      xor9ColumnBlocks47.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    47 (⟨xor9ColumnStart47, Xor9PackedCapture.blocks47, xor9ColumnSize47⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding47] at result
  exact result

theorem extent48 :
    (xor9ColumnBlocks48.toList.map Block.length).sum = xor9ColumnSize48 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    48 (⟨xor9ColumnStart48, Xor9PackedCapture.blocks48, xor9ColumnSize48⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding48] at result
  exact result

theorem output_part48 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart48
      xor9ColumnBlocks48.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    48 (⟨xor9ColumnStart48, Xor9PackedCapture.blocks48, xor9ColumnSize48⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding48] at result
  exact result

theorem extent49 :
    (xor9ColumnBlocks49.toList.map Block.length).sum = xor9ColumnSize49 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    49 (⟨xor9ColumnStart49, Xor9PackedCapture.blocks49, xor9ColumnSize49⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding49] at result
  exact result

theorem output_part49 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart49
      xor9ColumnBlocks49.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    49 (⟨xor9ColumnStart49, Xor9PackedCapture.blocks49, xor9ColumnSize49⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding49] at result
  exact result

theorem extent50 :
    (xor9ColumnBlocks50.toList.map Block.length).sum = xor9ColumnSize50 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    50 (⟨xor9ColumnStart50, Xor9PackedCapture.blocks50, xor9ColumnSize50⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding50] at result
  exact result

theorem output_part50 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart50
      xor9ColumnBlocks50.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    50 (⟨xor9ColumnStart50, Xor9PackedCapture.blocks50, xor9ColumnSize50⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding50] at result
  exact result

theorem extent51 :
    (xor9ColumnBlocks51.toList.map Block.length).sum = xor9ColumnSize51 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    51 (⟨xor9ColumnStart51, Xor9PackedCapture.blocks51, xor9ColumnSize51⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding51] at result
  exact result

theorem output_part51 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart51
      xor9ColumnBlocks51.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    51 (⟨xor9ColumnStart51, Xor9PackedCapture.blocks51, xor9ColumnSize51⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding51] at result
  exact result

theorem extent52 :
    (xor9ColumnBlocks52.toList.map Block.length).sum = xor9ColumnSize52 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    52 (⟨xor9ColumnStart52, Xor9PackedCapture.blocks52, xor9ColumnSize52⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding52] at result
  exact result

theorem output_part52 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart52
      xor9ColumnBlocks52.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    52 (⟨xor9ColumnStart52, Xor9PackedCapture.blocks52, xor9ColumnSize52⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding52] at result
  exact result

theorem extent53 :
    (xor9ColumnBlocks53.toList.map Block.length).sum = xor9ColumnSize53 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    53 (⟨xor9ColumnStart53, Xor9PackedCapture.blocks53, xor9ColumnSize53⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding53] at result
  exact result

theorem output_part53 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart53
      xor9ColumnBlocks53.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    53 (⟨xor9ColumnStart53, Xor9PackedCapture.blocks53, xor9ColumnSize53⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding53] at result
  exact result

theorem extent54 :
    (xor9ColumnBlocks54.toList.map Block.length).sum = xor9ColumnSize54 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    54 (⟨xor9ColumnStart54, Xor9PackedCapture.blocks54, xor9ColumnSize54⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding54] at result
  exact result

theorem output_part54 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart54
      xor9ColumnBlocks54.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    54 (⟨xor9ColumnStart54, Xor9PackedCapture.blocks54, xor9ColumnSize54⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding54] at result
  exact result

theorem extent55 :
    (xor9ColumnBlocks55.toList.map Block.length).sum = xor9ColumnSize55 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    55 (⟨xor9ColumnStart55, Xor9PackedCapture.blocks55, xor9ColumnSize55⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding55] at result
  exact result

theorem output_part55 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart55
      xor9ColumnBlocks55.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    55 (⟨xor9ColumnStart55, Xor9PackedCapture.blocks55, xor9ColumnSize55⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding55] at result
  exact result

theorem extent56 :
    (xor9ColumnBlocks56.toList.map Block.length).sum = xor9ColumnSize56 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    56 (⟨xor9ColumnStart56, Xor9PackedCapture.blocks56, xor9ColumnSize56⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding56] at result
  exact result

theorem output_part56 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart56
      xor9ColumnBlocks56.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    56 (⟨xor9ColumnStart56, Xor9PackedCapture.blocks56, xor9ColumnSize56⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding56] at result
  exact result

theorem extent57 :
    (xor9ColumnBlocks57.toList.map Block.length).sum = xor9ColumnSize57 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    57 (⟨xor9ColumnStart57, Xor9PackedCapture.blocks57, xor9ColumnSize57⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding57] at result
  exact result

theorem output_part57 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart57
      xor9ColumnBlocks57.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    57 (⟨xor9ColumnStart57, Xor9PackedCapture.blocks57, xor9ColumnSize57⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding57] at result
  exact result

theorem extent58 :
    (xor9ColumnBlocks58.toList.map Block.length).sum = xor9ColumnSize58 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    58 (⟨xor9ColumnStart58, Xor9PackedCapture.blocks58, xor9ColumnSize58⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding58] at result
  exact result

theorem output_part58 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart58
      xor9ColumnBlocks58.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    58 (⟨xor9ColumnStart58, Xor9PackedCapture.blocks58, xor9ColumnSize58⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding58] at result
  exact result

theorem extent59 :
    (xor9ColumnBlocks59.toList.map Block.length).sum = xor9ColumnSize59 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    59 (⟨xor9ColumnStart59, Xor9PackedCapture.blocks59, xor9ColumnSize59⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding59] at result
  exact result

theorem output_part59 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart59
      xor9ColumnBlocks59.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    59 (⟨xor9ColumnStart59, Xor9PackedCapture.blocks59, xor9ColumnSize59⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding59] at result
  exact result

theorem extent60 :
    (xor9ColumnBlocks60.toList.map Block.length).sum = xor9ColumnSize60 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    60 (⟨xor9ColumnStart60, Xor9PackedCapture.blocks60, xor9ColumnSize60⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding60] at result
  exact result

theorem output_part60 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart60
      xor9ColumnBlocks60.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    60 (⟨xor9ColumnStart60, Xor9PackedCapture.blocks60, xor9ColumnSize60⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding60] at result
  exact result

theorem extent61 :
    (xor9ColumnBlocks61.toList.map Block.length).sum = xor9ColumnSize61 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    61 (⟨xor9ColumnStart61, Xor9PackedCapture.blocks61, xor9ColumnSize61⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding61] at result
  exact result

theorem output_part61 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart61
      xor9ColumnBlocks61.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    61 (⟨xor9ColumnStart61, Xor9PackedCapture.blocks61, xor9ColumnSize61⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding61] at result
  exact result

theorem extent62 :
    (xor9ColumnBlocks62.toList.map Block.length).sum = xor9ColumnSize62 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    62 (⟨xor9ColumnStart62, Xor9PackedCapture.blocks62, xor9ColumnSize62⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding62] at result
  exact result

theorem output_part62 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart62
      xor9ColumnBlocks62.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    62 (⟨xor9ColumnStart62, Xor9PackedCapture.blocks62, xor9ColumnSize62⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding62] at result
  exact result

theorem extent63 :
    (xor9ColumnBlocks63.toList.map Block.length).sum = xor9ColumnSize63 := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    63 (⟨xor9ColumnStart63, Xor9PackedCapture.blocks63, xor9ColumnSize63⟩) (by rfl)).2
  rw [Xor9PackedCapture.binding63] at result
  exact result

theorem output_part63 :
    checkBlocks (fun n => n / 512 ^^^ n % 512) xor9ColumnStart63
      xor9ColumnBlocks63.toList = true := by
  have result := (PackedXor9Checks.requests_sound Xor9PackedCapture.requests Xor9PackedCapture.checked
    63 (⟨xor9ColumnStart63, Xor9PackedCapture.blocks63, xor9ColumnSize63⟩) (by rfl)).1
  rw [Xor9PackedCapture.binding63] at result
  exact result

theorem output_checks :
    checkBlocks (fun n => n / 512 ^^^ n % 512) 0
      (xor9Data.columns[2]'(by omega)).blocks.toList = true := by
  change checkBlocks (fun n => n / 512 ^^^ n % 512) 0 xor9Column.blocks.toList = true
  have joined : xor9Column.blocks = ((((((xor9ColumnBlocks0 ++ xor9ColumnBlocks1) ++ (xor9ColumnBlocks2 ++ xor9ColumnBlocks3)) ++ ((xor9ColumnBlocks4 ++ xor9ColumnBlocks5) ++ (xor9ColumnBlocks6 ++ xor9ColumnBlocks7))) ++ (((xor9ColumnBlocks8 ++ xor9ColumnBlocks9) ++ (xor9ColumnBlocks10 ++ xor9ColumnBlocks11)) ++ ((xor9ColumnBlocks12 ++ xor9ColumnBlocks13) ++ (xor9ColumnBlocks14 ++ xor9ColumnBlocks15)))) ++ ((((xor9ColumnBlocks16 ++ xor9ColumnBlocks17) ++ (xor9ColumnBlocks18 ++ xor9ColumnBlocks19)) ++ ((xor9ColumnBlocks20 ++ xor9ColumnBlocks21) ++ (xor9ColumnBlocks22 ++ xor9ColumnBlocks23))) ++ (((xor9ColumnBlocks24 ++ xor9ColumnBlocks25) ++ (xor9ColumnBlocks26 ++ xor9ColumnBlocks27)) ++ ((xor9ColumnBlocks28 ++ xor9ColumnBlocks29) ++ (xor9ColumnBlocks30 ++ xor9ColumnBlocks31))))) ++ (((((xor9ColumnBlocks32 ++ xor9ColumnBlocks33) ++ (xor9ColumnBlocks34 ++ xor9ColumnBlocks35)) ++ ((xor9ColumnBlocks36 ++ xor9ColumnBlocks37) ++ (xor9ColumnBlocks38 ++ xor9ColumnBlocks39))) ++ (((xor9ColumnBlocks40 ++ xor9ColumnBlocks41) ++ (xor9ColumnBlocks42 ++ xor9ColumnBlocks43)) ++ ((xor9ColumnBlocks44 ++ xor9ColumnBlocks45) ++ (xor9ColumnBlocks46 ++ xor9ColumnBlocks47)))) ++ ((((xor9ColumnBlocks48 ++ xor9ColumnBlocks49) ++ (xor9ColumnBlocks50 ++ xor9ColumnBlocks51)) ++ ((xor9ColumnBlocks52 ++ xor9ColumnBlocks53) ++ (xor9ColumnBlocks54 ++ xor9ColumnBlocks55))) ++ (((xor9ColumnBlocks56 ++ xor9ColumnBlocks57) ++ (xor9ColumnBlocks58 ++ xor9ColumnBlocks59)) ++ ((xor9ColumnBlocks60 ++ xor9ColumnBlocks61) ++ (xor9ColumnBlocks62 ++ xor9ColumnBlocks63)))))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    extent0, extent1, extent2, extent3, extent4, extent5, extent6, extent7, extent8, extent9, extent10, extent11, extent12, extent13, extent14, extent15, extent16, extent17, extent18, extent19, extent20, extent21, extent22, extent23, extent24, extent25, extent26, extent27, extent28, extent29, extent30, extent31, extent32, extent33, extent34, extent35, extent36, extent37, extent38, extent39, extent40, extent41, extent42, extent43, extent44, extent45, extent46, extent47, extent48, extent49, extent50, extent51, extent52, extent53, extent54, extent55, extent56, extent57, extent58, extent59, extent60, extent61, extent62,
    xor9ColumnSize0, xor9ColumnSize1, xor9ColumnSize2, xor9ColumnSize3, xor9ColumnSize4, xor9ColumnSize5, xor9ColumnSize6, xor9ColumnSize7, xor9ColumnSize8, xor9ColumnSize9, xor9ColumnSize10, xor9ColumnSize11, xor9ColumnSize12, xor9ColumnSize13, xor9ColumnSize14, xor9ColumnSize15, xor9ColumnSize16, xor9ColumnSize17, xor9ColumnSize18, xor9ColumnSize19, xor9ColumnSize20, xor9ColumnSize21, xor9ColumnSize22, xor9ColumnSize23, xor9ColumnSize24, xor9ColumnSize25, xor9ColumnSize26, xor9ColumnSize27, xor9ColumnSize28, xor9ColumnSize29, xor9ColumnSize30, xor9ColumnSize31, xor9ColumnSize32, xor9ColumnSize33, xor9ColumnSize34, xor9ColumnSize35, xor9ColumnSize36, xor9ColumnSize37, xor9ColumnSize38, xor9ColumnSize39, xor9ColumnSize40, xor9ColumnSize41, xor9ColumnSize42, xor9ColumnSize43, xor9ColumnSize44, xor9ColumnSize45, xor9ColumnSize46, xor9ColumnSize47, xor9ColumnSize48, xor9ColumnSize49, xor9ColumnSize50, xor9ColumnSize51, xor9ColumnSize52, xor9ColumnSize53, xor9ColumnSize54, xor9ColumnSize55, xor9ColumnSize56, xor9ColumnSize57, xor9ColumnSize58, xor9ColumnSize59, xor9ColumnSize60, xor9ColumnSize61, xor9ColumnSize62, Nat.reduceAdd]
  exact ⟨⟨⟨⟨⟨⟨output_part0, output_part1⟩, ⟨output_part2, output_part3⟩⟩, ⟨⟨output_part4, output_part5⟩, ⟨output_part6, output_part7⟩⟩⟩, ⟨⟨⟨output_part8, output_part9⟩, ⟨output_part10, output_part11⟩⟩, ⟨⟨output_part12, output_part13⟩, ⟨output_part14, output_part15⟩⟩⟩⟩, ⟨⟨⟨⟨output_part16, output_part17⟩, ⟨output_part18, output_part19⟩⟩, ⟨⟨output_part20, output_part21⟩, ⟨output_part22, output_part23⟩⟩⟩, ⟨⟨⟨output_part24, output_part25⟩, ⟨output_part26, output_part27⟩⟩, ⟨⟨output_part28, output_part29⟩, ⟨output_part30, output_part31⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨output_part32, output_part33⟩, ⟨output_part34, output_part35⟩⟩, ⟨⟨output_part36, output_part37⟩, ⟨output_part38, output_part39⟩⟩⟩, ⟨⟨⟨output_part40, output_part41⟩, ⟨output_part42, output_part43⟩⟩, ⟨⟨output_part44, output_part45⟩, ⟨output_part46, output_part47⟩⟩⟩⟩, ⟨⟨⟨⟨output_part48, output_part49⟩, ⟨output_part50, output_part51⟩⟩, ⟨⟨output_part52, output_part53⟩, ⟨output_part54, output_part55⟩⟩⟩, ⟨⟨⟨output_part56, output_part57⟩, ⟨output_part58, output_part59⟩⟩, ⟨⟨output_part60, output_part61⟩, ⟨output_part62, output_part63⟩⟩⟩⟩⟩⟩

end Airbender.Blake2G.Proofs.Xor9Certificate
