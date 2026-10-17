import Airbender.Proofs.Tables.ShiftOutputExtent0
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part0
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part1
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part2
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part3
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part4
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part5
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part6
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part7
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part8
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part9
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part10
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part11
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part12
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part13
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part14
import Airbender.Proofs.Tables.ShiftOutputCertificate0Part15

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 0

theorem output0_checks :
    checkBlocks (outputByte 0) 0 byteShiftColumn4.blocks.toList = true := by
  have joined : byteShiftColumn4.blocks = ((((output0Blocks0 ++ output0Blocks1) ++ (output0Blocks2 ++ output0Blocks3)) ++ ((output0Blocks4 ++ output0Blocks5) ++ (output0Blocks6 ++ output0Blocks7))) ++ (((output0Blocks8 ++ output0Blocks9) ++ (output0Blocks10 ++ output0Blocks11)) ++ ((output0Blocks12 ++ output0Blocks13) ++ (output0Blocks14 ++ output0Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output0_extent0, output0_extent1, output0_extent2, output0_extent3, output0_extent4, output0_extent5, output0_extent6, output0_extent7, output0_extent8, output0_extent9, output0_extent10, output0_extent11, output0_extent12, output0_extent13, output0_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output0_part0, output0_part1⟩, ⟨output0_part2, output0_part3⟩⟩, ⟨⟨output0_part4, output0_part5⟩, ⟨output0_part6, output0_part7⟩⟩⟩, ⟨⟨⟨output0_part8, output0_part9⟩, ⟨output0_part10, output0_part11⟩⟩, ⟨⟨output0_part12, output0_part13⟩, ⟨output0_part14, output0_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
