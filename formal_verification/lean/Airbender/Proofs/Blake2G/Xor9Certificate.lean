import Airbender.Proofs.Blake2G.Xor9Extents
import Airbender.Proofs.Blake2G.Xor9CertificatePart0
import Airbender.Proofs.Blake2G.Xor9CertificatePart1
import Airbender.Proofs.Blake2G.Xor9CertificatePart2
import Airbender.Proofs.Blake2G.Xor9CertificatePart3
import Airbender.Proofs.Blake2G.Xor9CertificatePart4
import Airbender.Proofs.Blake2G.Xor9CertificatePart5
import Airbender.Proofs.Blake2G.Xor9CertificatePart6
import Airbender.Proofs.Blake2G.Xor9CertificatePart7
import Airbender.Proofs.Blake2G.Xor9CertificatePart8
import Airbender.Proofs.Blake2G.Xor9CertificatePart9
import Airbender.Proofs.Blake2G.Xor9CertificatePart10
import Airbender.Proofs.Blake2G.Xor9CertificatePart11
import Airbender.Proofs.Blake2G.Xor9CertificatePart12
import Airbender.Proofs.Blake2G.Xor9CertificatePart13
import Airbender.Proofs.Blake2G.Xor9CertificatePart14
import Airbender.Proofs.Blake2G.Xor9CertificatePart15
import Airbender.Proofs.Blake2G.Xor9CertificatePart16
import Airbender.Proofs.Blake2G.Xor9CertificatePart17
import Airbender.Proofs.Blake2G.Xor9CertificatePart18
import Airbender.Proofs.Blake2G.Xor9CertificatePart19
import Airbender.Proofs.Blake2G.Xor9CertificatePart20
import Airbender.Proofs.Blake2G.Xor9CertificatePart21
import Airbender.Proofs.Blake2G.Xor9CertificatePart22
import Airbender.Proofs.Blake2G.Xor9CertificatePart23
import Airbender.Proofs.Blake2G.Xor9CertificatePart24
import Airbender.Proofs.Blake2G.Xor9CertificatePart25
import Airbender.Proofs.Blake2G.Xor9CertificatePart26
import Airbender.Proofs.Blake2G.Xor9CertificatePart27
import Airbender.Proofs.Blake2G.Xor9CertificatePart28
import Airbender.Proofs.Blake2G.Xor9CertificatePart29
import Airbender.Proofs.Blake2G.Xor9CertificatePart30
import Airbender.Proofs.Blake2G.Xor9CertificatePart31
import Airbender.Proofs.Blake2G.Xor9CertificatePart32
import Airbender.Proofs.Blake2G.Xor9CertificatePart33
import Airbender.Proofs.Blake2G.Xor9CertificatePart34
import Airbender.Proofs.Blake2G.Xor9CertificatePart35
import Airbender.Proofs.Blake2G.Xor9CertificatePart36
import Airbender.Proofs.Blake2G.Xor9CertificatePart37
import Airbender.Proofs.Blake2G.Xor9CertificatePart38
import Airbender.Proofs.Blake2G.Xor9CertificatePart39
import Airbender.Proofs.Blake2G.Xor9CertificatePart40
import Airbender.Proofs.Blake2G.Xor9CertificatePart41
import Airbender.Proofs.Blake2G.Xor9CertificatePart42
import Airbender.Proofs.Blake2G.Xor9CertificatePart43
import Airbender.Proofs.Blake2G.Xor9CertificatePart44
import Airbender.Proofs.Blake2G.Xor9CertificatePart45
import Airbender.Proofs.Blake2G.Xor9CertificatePart46
import Airbender.Proofs.Blake2G.Xor9CertificatePart47
import Airbender.Proofs.Blake2G.Xor9CertificatePart48
import Airbender.Proofs.Blake2G.Xor9CertificatePart49
import Airbender.Proofs.Blake2G.Xor9CertificatePart50
import Airbender.Proofs.Blake2G.Xor9CertificatePart51
import Airbender.Proofs.Blake2G.Xor9CertificatePart52
import Airbender.Proofs.Blake2G.Xor9CertificatePart53
import Airbender.Proofs.Blake2G.Xor9CertificatePart54
import Airbender.Proofs.Blake2G.Xor9CertificatePart55
import Airbender.Proofs.Blake2G.Xor9CertificatePart56
import Airbender.Proofs.Blake2G.Xor9CertificatePart57
import Airbender.Proofs.Blake2G.Xor9CertificatePart58
import Airbender.Proofs.Blake2G.Xor9CertificatePart59
import Airbender.Proofs.Blake2G.Xor9CertificatePart60
import Airbender.Proofs.Blake2G.Xor9CertificatePart61
import Airbender.Proofs.Blake2G.Xor9CertificatePart62
import Airbender.Proofs.Blake2G.Xor9CertificatePart63

namespace Airbender.Blake2G.Proofs.Xor9Certificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

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
