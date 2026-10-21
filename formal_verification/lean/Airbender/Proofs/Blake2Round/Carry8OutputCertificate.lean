import Airbender.Proofs.Blake2Round.Carry8OutputPart0
import Airbender.Proofs.Blake2Round.Carry8OutputPart1
import Airbender.Proofs.Blake2Round.Carry8OutputPart2
import Airbender.Proofs.Blake2Round.Carry8OutputPart3
import Airbender.Proofs.Blake2Round.Carry8OutputPart4
import Airbender.Proofs.Blake2Round.Carry8OutputPart5
import Airbender.Proofs.Blake2Round.Carry8OutputPart6
import Airbender.Proofs.Blake2Round.Carry8OutputPart7
import Airbender.Proofs.Blake2Round.Carry8OutputPart8
import Airbender.Proofs.Blake2Round.Carry8OutputPart9
import Airbender.Proofs.Blake2Round.Carry8OutputPart10
import Airbender.Proofs.Blake2Round.Carry8OutputPart11
import Airbender.Proofs.Blake2Round.Carry8OutputPart12
import Airbender.Proofs.Blake2Round.Carry8OutputPart13
import Airbender.Proofs.Blake2Round.Carry8OutputPart14
import Airbender.Proofs.Blake2Round.Carry8OutputPart15
import Airbender.Proofs.Blake2Round.Carry8OutputPart16
import Airbender.Proofs.Blake2Round.Carry8OutputPart17
import Airbender.Proofs.Blake2Round.Carry8OutputPart18
import Airbender.Proofs.Blake2Round.Carry8OutputPart19
import Airbender.Proofs.Blake2Round.Carry8OutputPart20
import Airbender.Proofs.Blake2Round.Carry8OutputPart21
import Airbender.Proofs.Blake2Round.Carry8OutputPart22
import Airbender.Proofs.Blake2Round.Carry8OutputPart23
import Airbender.Proofs.Blake2Round.Carry8OutputPart24
import Airbender.Proofs.Blake2Round.Carry8OutputPart25
import Airbender.Proofs.Blake2Round.Carry8OutputPart26
import Airbender.Proofs.Blake2Round.Carry8OutputPart27
import Airbender.Proofs.Blake2Round.Carry8OutputPart28
import Airbender.Proofs.Blake2Round.Carry8OutputPart29
import Airbender.Proofs.Blake2Round.Carry8OutputPart30
import Airbender.Proofs.Blake2Round.Carry8OutputPart31

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs Carry8Certificate
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Assemble bounded kernel certificates for every actual imported output block. -/
theorem carry8_output_checks :
    checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) 0
      xor8CarryData.columns[3].blocks.toList = true := by
  change checkBlocks (fun n => n / 256 % 256 ^^^ n % 256) 0 carry8Column.blocks.toList = true
  have joined : carry8Column.blocks = (((((carry8ColumnBlocks0 ++ carry8ColumnBlocks1) ++ (carry8ColumnBlocks2 ++ carry8ColumnBlocks3)) ++ ((carry8ColumnBlocks4 ++ carry8ColumnBlocks5) ++ (carry8ColumnBlocks6 ++ carry8ColumnBlocks7))) ++ (((carry8ColumnBlocks8 ++ carry8ColumnBlocks9) ++ (carry8ColumnBlocks10 ++ carry8ColumnBlocks11)) ++ ((carry8ColumnBlocks12 ++ carry8ColumnBlocks13) ++ (carry8ColumnBlocks14 ++ carry8ColumnBlocks15)))) ++ ((((carry8ColumnBlocks16 ++ carry8ColumnBlocks17) ++ (carry8ColumnBlocks18 ++ carry8ColumnBlocks19)) ++ ((carry8ColumnBlocks20 ++ carry8ColumnBlocks21) ++ (carry8ColumnBlocks22 ++ carry8ColumnBlocks23))) ++ (((carry8ColumnBlocks24 ++ carry8ColumnBlocks25) ++ (carry8ColumnBlocks26 ++ carry8ColumnBlocks27)) ++ ((carry8ColumnBlocks28 ++ carry8ColumnBlocks29) ++ (carry8ColumnBlocks30 ++ carry8ColumnBlocks31))))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    extent0, extent1, extent2, extent3, extent4, extent5, extent6, extent7, extent8, extent9, extent10, extent11, extent12, extent13, extent14, extent15, extent16, extent17, extent18, extent19, extent20, extent21, extent22, extent23, extent24, extent25, extent26, extent27, extent28, extent29, extent30,
    carry8ColumnSize0, carry8ColumnSize1, carry8ColumnSize2, carry8ColumnSize3, carry8ColumnSize4, carry8ColumnSize5, carry8ColumnSize6, carry8ColumnSize7, carry8ColumnSize8, carry8ColumnSize9, carry8ColumnSize10, carry8ColumnSize11, carry8ColumnSize12, carry8ColumnSize13, carry8ColumnSize14, carry8ColumnSize15, carry8ColumnSize16, carry8ColumnSize17, carry8ColumnSize18, carry8ColumnSize19, carry8ColumnSize20, carry8ColumnSize21, carry8ColumnSize22, carry8ColumnSize23, carry8ColumnSize24, carry8ColumnSize25, carry8ColumnSize26, carry8ColumnSize27, carry8ColumnSize28, carry8ColumnSize29, carry8ColumnSize30,  Nat.reduceAdd]
  exact ⟨⟨⟨⟨⟨output_part0, output_part1⟩, ⟨output_part2, output_part3⟩⟩, ⟨⟨output_part4, output_part5⟩, ⟨output_part6, output_part7⟩⟩⟩, ⟨⟨⟨output_part8, output_part9⟩, ⟨output_part10, output_part11⟩⟩, ⟨⟨output_part12, output_part13⟩, ⟨output_part14, output_part15⟩⟩⟩⟩, ⟨⟨⟨⟨output_part16, output_part17⟩, ⟨output_part18, output_part19⟩⟩, ⟨⟨output_part20, output_part21⟩, ⟨output_part22, output_part23⟩⟩⟩, ⟨⟨⟨output_part24, output_part25⟩, ⟨output_part26, output_part27⟩⟩, ⟨⟨output_part28, output_part29⟩, ⟨output_part30, output_part31⟩⟩⟩⟩⟩

end Airbender.Blake2Round.Proofs
