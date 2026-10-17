import Airbender.Proofs.Tables.ShiftOutputExtent2
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part0
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part1
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part2
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part3
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part4
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part5
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part6
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part7
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part8
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part9
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part10
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part11
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part12
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part13
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part14
import Airbender.Proofs.Tables.ShiftOutputCertificate2Part15

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output2_checks :
    checkBlocks (outputByte 2) 0 byteShiftColumn6.blocks.toList = true := by
  have joined : byteShiftColumn6.blocks = ((((output2Blocks0 ++ output2Blocks1) ++ (output2Blocks2 ++ output2Blocks3)) ++ ((output2Blocks4 ++ output2Blocks5) ++ (output2Blocks6 ++ output2Blocks7))) ++ (((output2Blocks8 ++ output2Blocks9) ++ (output2Blocks10 ++ output2Blocks11)) ++ ((output2Blocks12 ++ output2Blocks13) ++ (output2Blocks14 ++ output2Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output2_extent0, output2_extent1, output2_extent2, output2_extent3, output2_extent4, output2_extent5, output2_extent6, output2_extent7, output2_extent8, output2_extent9, output2_extent10, output2_extent11, output2_extent12, output2_extent13, output2_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output2_part0, output2_part1⟩, ⟨output2_part2, output2_part3⟩⟩, ⟨⟨output2_part4, output2_part5⟩, ⟨output2_part6, output2_part7⟩⟩⟩, ⟨⟨⟨output2_part8, output2_part9⟩, ⟨output2_part10, output2_part11⟩⟩, ⟨⟨output2_part12, output2_part13⟩, ⟨output2_part14, output2_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
