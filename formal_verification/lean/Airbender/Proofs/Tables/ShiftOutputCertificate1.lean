import Airbender.Proofs.Tables.ShiftOutputExtent1
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part0
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part1
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part2
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part3
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part4
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part5
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part6
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part7
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part8
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part9
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part10
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part11
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part12
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part13
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part14
import Airbender.Proofs.Tables.ShiftOutputCertificate1Part15

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output1_checks :
    checkBlocks (outputByte 1) 0 byteShiftColumn5.blocks.toList = true := by
  have joined : byteShiftColumn5.blocks = ((((output1Blocks0 ++ output1Blocks1) ++ (output1Blocks2 ++ output1Blocks3)) ++ ((output1Blocks4 ++ output1Blocks5) ++ (output1Blocks6 ++ output1Blocks7))) ++ (((output1Blocks8 ++ output1Blocks9) ++ (output1Blocks10 ++ output1Blocks11)) ++ ((output1Blocks12 ++ output1Blocks13) ++ (output1Blocks14 ++ output1Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output1_extent0, output1_extent1, output1_extent2, output1_extent3, output1_extent4, output1_extent5, output1_extent6, output1_extent7, output1_extent8, output1_extent9, output1_extent10, output1_extent11, output1_extent12, output1_extent13, output1_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output1_part0, output1_part1⟩, ⟨output1_part2, output1_part3⟩⟩, ⟨⟨output1_part4, output1_part5⟩, ⟨output1_part6, output1_part7⟩⟩⟩, ⟨⟨⟨output1_part8, output1_part9⟩, ⟨output1_part10, output1_part11⟩⟩, ⟨⟨output1_part12, output1_part13⟩, ⟨output1_part14, output1_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
