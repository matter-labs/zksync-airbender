import Airbender.Proofs.Tables.ShiftOutputExtent2
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column2

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

private theorem all_parts :
    ((((checkBlocks (outputByte 2) 0 output2Blocks0.toList = true ∧ checkBlocks (outputByte 2) 17522 output2Blocks1.toList = true) ∧ (checkBlocks (outputByte 2) 32386 output2Blocks2.toList = true ∧ checkBlocks (outputByte 2) 46250 output2Blocks3.toList = true)) ∧ ((checkBlocks (outputByte 2) 60242 output2Blocks4.toList = true ∧ checkBlocks (outputByte 2) 75866 output2Blocks5.toList = true) ∧ (checkBlocks (outputByte 2) 90170 output2Blocks6.toList = true ∧ checkBlocks (outputByte 2) 104034 output2Blocks7.toList = true))) ∧ (((checkBlocks (outputByte 2) 118026 output2Blocks8.toList = true ∧ checkBlocks (outputByte 2) 132642 output2Blocks9.toList = true) ∧ (checkBlocks (outputByte 2) 159236 output2Blocks10.toList = true ∧ checkBlocks (outputByte 2) 183812 output2Blocks11.toList = true)) ∧ ((checkBlocks (outputByte 2) 205628 output2Blocks12.toList = true ∧ checkBlocks (outputByte 2) 221028 output2Blocks13.toList = true) ∧ (checkBlocks (outputByte 2) 235346 output2Blocks14.toList = true ∧ checkBlocks (outputByte 2) 248698 output2Blocks15.toList = true)))) := by
  have result := ShiftPackedEncoding.Lane2.native_checks
  have joined : byteShiftColumn6.blocks = ((((output2Blocks0 ++ output2Blocks1) ++ (output2Blocks2 ++ output2Blocks3)) ++ ((output2Blocks4 ++ output2Blocks5) ++ (output2Blocks6 ++ output2Blocks7))) ++ (((output2Blocks8 ++ output2Blocks9) ++ (output2Blocks10 ++ output2Blocks11)) ++ ((output2Blocks12 ++ output2Blocks13) ++ (output2Blocks14 ++ output2Blocks15)))) := rfl
  rw [joined] at result
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output2_extent0, output2_extent1, output2_extent2, output2_extent3, output2_extent4, output2_extent5, output2_extent6, output2_extent7, output2_extent8, output2_extent9, output2_extent10, output2_extent11, output2_extent12, output2_extent13, output2_extent14, Nat.reduceAdd] at result
  exact result

theorem output2_part0 :
    checkBlocks (outputByte 2) 0 output2Blocks0.toList = true := all_parts.1.1.1.1

theorem output2_part1 :
    checkBlocks (outputByte 2) 17522 output2Blocks1.toList = true := all_parts.1.1.1.2

theorem output2_part2 :
    checkBlocks (outputByte 2) 32386 output2Blocks2.toList = true := all_parts.1.1.2.1

theorem output2_part3 :
    checkBlocks (outputByte 2) 46250 output2Blocks3.toList = true := all_parts.1.1.2.2

theorem output2_part4 :
    checkBlocks (outputByte 2) 60242 output2Blocks4.toList = true := all_parts.1.2.1.1

theorem output2_part5 :
    checkBlocks (outputByte 2) 75866 output2Blocks5.toList = true := all_parts.1.2.1.2

theorem output2_part6 :
    checkBlocks (outputByte 2) 90170 output2Blocks6.toList = true := all_parts.1.2.2.1

theorem output2_part7 :
    checkBlocks (outputByte 2) 104034 output2Blocks7.toList = true := all_parts.1.2.2.2

theorem output2_part8 :
    checkBlocks (outputByte 2) 118026 output2Blocks8.toList = true := all_parts.2.1.1.1

theorem output2_part9 :
    checkBlocks (outputByte 2) 132642 output2Blocks9.toList = true := all_parts.2.1.1.2

theorem output2_part10 :
    checkBlocks (outputByte 2) 159236 output2Blocks10.toList = true := all_parts.2.1.2.1

theorem output2_part11 :
    checkBlocks (outputByte 2) 183812 output2Blocks11.toList = true := all_parts.2.1.2.2

theorem output2_part12 :
    checkBlocks (outputByte 2) 205628 output2Blocks12.toList = true := all_parts.2.2.1.1

theorem output2_part13 :
    checkBlocks (outputByte 2) 221028 output2Blocks13.toList = true := all_parts.2.2.1.2

theorem output2_part14 :
    checkBlocks (outputByte 2) 235346 output2Blocks14.toList = true := all_parts.2.2.2.1

theorem output2_part15 :
    checkBlocks (outputByte 2) 248698 output2Blocks15.toList = true := all_parts.2.2.2.2

theorem output2_checks :
    checkBlocks (outputByte 2) 0 byteShiftColumn6.blocks.toList = true := by
  have joined : byteShiftColumn6.blocks = ((((output2Blocks0 ++ output2Blocks1) ++ (output2Blocks2 ++ output2Blocks3)) ++ ((output2Blocks4 ++ output2Blocks5) ++ (output2Blocks6 ++ output2Blocks7))) ++ (((output2Blocks8 ++ output2Blocks9) ++ (output2Blocks10 ++ output2Blocks11)) ++ ((output2Blocks12 ++ output2Blocks13) ++ (output2Blocks14 ++ output2Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output2_extent0, output2_extent1, output2_extent2, output2_extent3, output2_extent4, output2_extent5, output2_extent6, output2_extent7, output2_extent8, output2_extent9, output2_extent10, output2_extent11, output2_extent12, output2_extent13, output2_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output2_part0, output2_part1⟩, ⟨output2_part2, output2_part3⟩⟩, ⟨⟨output2_part4, output2_part5⟩, ⟨output2_part6, output2_part7⟩⟩⟩, ⟨⟨⟨output2_part8, output2_part9⟩, ⟨output2_part10, output2_part11⟩⟩, ⟨⟨output2_part12, output2_part13⟩, ⟨output2_part14, output2_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
