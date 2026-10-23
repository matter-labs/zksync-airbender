import Airbender.Proofs.Blake2Round.Carry8Extents
import Airbender.Proofs.Blake2G.Xor8Certificate
import Airbender.Proofs.Tables.CyclicXorCertificate

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs Carry8Certificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000
@[irreducible] private noncomputable def byteBlocks : List Block :=
  (Blake2G.xor8Data.columns[2]'(by decide)).blocks.toList

private theorem head : byteBlocks = .affine 256 0 1 :: byteBlocks.tail := by
  unfold byteBlocks
  dsimp only [xor8CarryData, Blake2G.xor8Data, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  all_goals rfl

private theorem shape : xor8CarryData.columns[3].blocks.toList =
    .affine 1 0 0 :: .affine 255 1 1 ::
      (byteBlocks.tail ++ (byteBlocks ++ byteBlocks)) := by
  unfold byteBlocks
  dsimp only [xor8CarryData, Blake2G.xor8Data, Vector.getElem_mk,
    Fin.getElem_fin, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [raw_toList_append, List.cons_append, List.nil_append]
  all_goals rfl

private theorem nativeColumn : xor8CarryData.columns[3].blocks = carry8Column.blocks := by
  dsimp only [xor8CarryData, carry8Column, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]


private theorem full_extent : (carry8Column.blocks.toList.map Block.length).sum = 196608 := by
  have joined : carry8Column.blocks = (((((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ++ ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7))) ++ (((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ++ ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15)))) ++ ((((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ++ ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23))) ++ (((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ++ ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31))))) := rfl
  exact (congrArg (fun blocks : Array Block => (blocks.toList.map Block.length).sum) joined).trans
    (array_extent_join ((((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ++ ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7))) ++ (((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ++ ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15)))) ((((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ++ ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23))) ++ (((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ++ ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31)))) (array_extent_join (((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ++ ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7))) (((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ++ ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15))) (array_extent_join ((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7)) (array_extent_join (carry8ColumnBlocks0 ++ carry8ColumnBlocks1) (carry8ColumnBlocks2 ++ carry8ColumnBlocks3) (array_extent_join carry8ColumnBlocks0 carry8ColumnBlocks1 extent0 extent1) (array_extent_join carry8ColumnBlocks2 carry8ColumnBlocks3 extent2 extent3)) (array_extent_join (carry8ColumnBlocks4 ++ carry8ColumnBlocks5) (carry8ColumnBlocks6 ++ carry8ColumnBlocks7) (array_extent_join carry8ColumnBlocks4 carry8ColumnBlocks5 extent4 extent5) (array_extent_join carry8ColumnBlocks6 carry8ColumnBlocks7 extent6 extent7))) (array_extent_join ((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15)) (array_extent_join (carry8ColumnBlocks8 ++ carry8ColumnBlocks9) (carry8ColumnBlocks10 ++ carry8ColumnBlocks11) (array_extent_join carry8ColumnBlocks8 carry8ColumnBlocks9 extent8 extent9) (array_extent_join carry8ColumnBlocks10 carry8ColumnBlocks11 extent10 extent11)) (array_extent_join (carry8ColumnBlocks12 ++ carry8ColumnBlocks13) (carry8ColumnBlocks14 ++ carry8ColumnBlocks15) (array_extent_join carry8ColumnBlocks12 carry8ColumnBlocks13 extent12 extent13) (array_extent_join carry8ColumnBlocks14 carry8ColumnBlocks15 extent14 extent15)))) (array_extent_join (((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ++ ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23))) (((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ++ ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31))) (array_extent_join ((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23)) (array_extent_join (carry8ColumnBlocks16 ++ carry8ColumnBlocks17) (carry8ColumnBlocks18 ++ carry8ColumnBlocks19) (array_extent_join carry8ColumnBlocks16 carry8ColumnBlocks17 extent16 extent17) (array_extent_join carry8ColumnBlocks18 carry8ColumnBlocks19 extent18 extent19)) (array_extent_join (carry8ColumnBlocks20 ++ carry8ColumnBlocks21) (carry8ColumnBlocks22 ++ carry8ColumnBlocks23) (array_extent_join carry8ColumnBlocks20 carry8ColumnBlocks21 extent20 extent21) (array_extent_join carry8ColumnBlocks22 carry8ColumnBlocks23 extent22 extent23))) (array_extent_join ((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31)) (array_extent_join (carry8ColumnBlocks24 ++ carry8ColumnBlocks25) (carry8ColumnBlocks26 ++ carry8ColumnBlocks27) (array_extent_join carry8ColumnBlocks24 carry8ColumnBlocks25 extent24 extent25) (array_extent_join carry8ColumnBlocks26 carry8ColumnBlocks27 extent26 extent27)) (array_extent_join (carry8ColumnBlocks28 ++ carry8ColumnBlocks29) (carry8ColumnBlocks30 ++ carry8ColumnBlocks31) (array_extent_join carry8ColumnBlocks28 carry8ColumnBlocks29 extent28 extent29) (array_extent_join carry8ColumnBlocks30 carry8ColumnBlocks31 extent30 extent31)))))

/-- Exact coverage of the native byte carry output column. -/
theorem carry8_output_extent :
    (xor8CarryData.columns[3].blocks.toList.map Block.length).sum = 196608 := by
  rw [nativeColumn]
  exact full_extent

/-- Reuse the checked byte-XOR certificate after checking the native column shape. -/
theorem carry8_output_checks :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) 0
      xor8CarryData.columns[3].blocks.toList = true := by
  have checked : checkBlocks (fun n => n / 256 ^^^ n % 256) 0 byteBlocks = true := by
    unfold byteBlocks
    exact Blake2G.Proofs.XorCertificate.output8
  apply cyclic_xor8_check byteBlocks _ head shape
  · exact carry8_output_extent
  · exact checked

/-- The original partition interfaces are projections of the one shared check. -/
theorem Carry8Certificate.output_parts :
    ((((((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart0
      carry8ColumnBlocks0.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart1
      carry8ColumnBlocks1.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart2
      carry8ColumnBlocks2.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart3
      carry8ColumnBlocks3.toList = true))) ∧ (((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart4
      carry8ColumnBlocks4.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart5
      carry8ColumnBlocks5.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart6
      carry8ColumnBlocks6.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart7
      carry8ColumnBlocks7.toList = true)))) ∧ ((((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart8
      carry8ColumnBlocks8.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart9
      carry8ColumnBlocks9.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart10
      carry8ColumnBlocks10.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart11
      carry8ColumnBlocks11.toList = true))) ∧ (((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart12
      carry8ColumnBlocks12.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart13
      carry8ColumnBlocks13.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart14
      carry8ColumnBlocks14.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart15
      carry8ColumnBlocks15.toList = true))))) ∧ (((((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart16
      carry8ColumnBlocks16.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart17
      carry8ColumnBlocks17.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart18
      carry8ColumnBlocks18.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart19
      carry8ColumnBlocks19.toList = true))) ∧ (((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart20
      carry8ColumnBlocks20.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart21
      carry8ColumnBlocks21.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart22
      carry8ColumnBlocks22.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart23
      carry8ColumnBlocks23.toList = true)))) ∧ ((((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart24
      carry8ColumnBlocks24.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart25
      carry8ColumnBlocks25.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart26
      carry8ColumnBlocks26.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart27
      carry8ColumnBlocks27.toList = true))) ∧ (((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart28
      carry8ColumnBlocks28.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart29
      carry8ColumnBlocks29.toList = true)) ∧ ((checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart30
      carry8ColumnBlocks30.toList = true) ∧ (checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) carry8ColumnStart31
      carry8ColumnBlocks31.toList = true)))))) := by
  have checked : checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) 0
      carry8Column.blocks.toList = true := by
    rw [← nativeColumn]
    exact carry8_output_checks
  have joined : carry8Column.blocks = (((((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ++ ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7))) ++ (((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ++ ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15)))) ++ ((((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ++ ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23))) ++ (((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ++ ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31))))) := rfl
  rw [joined] at checked
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    extent0, extent1, extent2, extent3, extent4, extent5, extent6, extent7, extent8, extent9, extent10, extent11, extent12, extent13, extent14, extent15, extent16, extent17, extent18, extent19, extent20, extent21, extent22, extent23, extent24, extent25, extent26, extent27, extent28, extent29, extent30,
    carry8ColumnSize0, carry8ColumnSize1, carry8ColumnSize2, carry8ColumnSize3, carry8ColumnSize4, carry8ColumnSize5, carry8ColumnSize6, carry8ColumnSize7, carry8ColumnSize8, carry8ColumnSize9, carry8ColumnSize10, carry8ColumnSize11, carry8ColumnSize12, carry8ColumnSize13, carry8ColumnSize14, carry8ColumnSize15, carry8ColumnSize16, carry8ColumnSize17, carry8ColumnSize18, carry8ColumnSize19, carry8ColumnSize20, carry8ColumnSize21, carry8ColumnSize22, carry8ColumnSize23, carry8ColumnSize24, carry8ColumnSize25, carry8ColumnSize26, carry8ColumnSize27, carry8ColumnSize28, carry8ColumnSize29, carry8ColumnSize30,  Nat.reduceAdd] at checked
  exact checked

end Airbender.Blake2Round.Proofs
