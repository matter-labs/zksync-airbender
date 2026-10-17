import Airbender.Proofs.Tables.ShiftOutputExtent3
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part0
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part1
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part2
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part3
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part4
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part5
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part6
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part7
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part8
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part9
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part10
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part11
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part12
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part13
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part14
import Airbender.Proofs.Tables.ShiftOutputCertificate3Part15

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output3_checks :
    checkBlocks (outputByte 3) 0 byteShiftColumn7.blocks.toList = true := by
  have joined : byteShiftColumn7.blocks = ((((output3Blocks0 ++ output3Blocks1) ++ (output3Blocks2 ++ output3Blocks3)) ++ ((output3Blocks4 ++ output3Blocks5) ++ (output3Blocks6 ++ output3Blocks7))) ++ (((output3Blocks8 ++ output3Blocks9) ++ (output3Blocks10 ++ output3Blocks11)) ++ ((output3Blocks12 ++ output3Blocks13) ++ (output3Blocks14 ++ output3Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output3_extent0, output3_extent1, output3_extent2, output3_extent3, output3_extent4, output3_extent5, output3_extent6, output3_extent7, output3_extent8, output3_extent9, output3_extent10, output3_extent11, output3_extent12, output3_extent13, output3_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output3_part0, output3_part1⟩, ⟨output3_part2, output3_part3⟩⟩, ⟨⟨output3_part4, output3_part5⟩, ⟨output3_part6, output3_part7⟩⟩⟩, ⟨⟨⟨output3_part8, output3_part9⟩, ⟨output3_part10, output3_part11⟩⟩, ⟨⟨output3_part12, output3_part13⟩, ⟨output3_part14, output3_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
