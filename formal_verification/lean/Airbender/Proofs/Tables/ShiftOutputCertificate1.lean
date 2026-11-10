import Airbender.Proofs.Tables.ShiftOutputExtent1
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column1

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

private theorem all_parts :
    ((((checkBlocks (outputByte 1) 0 output1Blocks0.toList = true ∧ checkBlocks (outputByte 1) 17682 output1Blocks1.toList = true) ∧ (checkBlocks (outputByte 1) 32602 output1Blocks2.toList = true ∧ checkBlocks (outputByte 1) 46666 output1Blocks3.toList = true)) ∧ ((checkBlocks (outputByte 1) 60722 output1Blocks4.toList = true ∧ checkBlocks (outputByte 1) 83484 output1Blocks5.toList = true) ∧ (checkBlocks (outputByte 1) 108860 output1Blocks6.toList = true ∧ checkBlocks (outputByte 1) 133382 output1Blocks7.toList = true))) ∧ (((checkBlocks (outputByte 1) 148828 output1Blocks8.toList = true ∧ checkBlocks (outputByte 1) 162868 output1Blocks9.toList = true) ∧ (checkBlocks (outputByte 1) 175964 output1Blocks10.toList = true ∧ checkBlocks (outputByte 1) 189052 output1Blocks11.toList = true)) ∧ ((checkBlocks (outputByte 1) 204972 output1Blocks12.toList = true ∧ checkBlocks (outputByte 1) 220756 output1Blocks13.toList = true) ∧ (checkBlocks (outputByte 1) 235148 output1Blocks14.toList = true ∧ checkBlocks (outputByte 1) 248698 output1Blocks15.toList = true)))) := by
  have result := ShiftPackedEncoding.Lane1.native_checks
  have joined : byteShiftColumn5.blocks = ((((output1Blocks0 ++ output1Blocks1) ++ (output1Blocks2 ++ output1Blocks3)) ++ ((output1Blocks4 ++ output1Blocks5) ++ (output1Blocks6 ++ output1Blocks7))) ++ (((output1Blocks8 ++ output1Blocks9) ++ (output1Blocks10 ++ output1Blocks11)) ++ ((output1Blocks12 ++ output1Blocks13) ++ (output1Blocks14 ++ output1Blocks15)))) := rfl
  rw [joined] at result
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output1_extent0, output1_extent1, output1_extent2, output1_extent3, output1_extent4, output1_extent5, output1_extent6, output1_extent7, output1_extent8, output1_extent9, output1_extent10, output1_extent11, output1_extent12, output1_extent13, output1_extent14, Nat.reduceAdd] at result
  exact result

theorem output1_part0 :
    checkBlocks (outputByte 1) 0 output1Blocks0.toList = true := all_parts.1.1.1.1

theorem output1_part1 :
    checkBlocks (outputByte 1) 17682 output1Blocks1.toList = true := all_parts.1.1.1.2

theorem output1_part2 :
    checkBlocks (outputByte 1) 32602 output1Blocks2.toList = true := all_parts.1.1.2.1

theorem output1_part3 :
    checkBlocks (outputByte 1) 46666 output1Blocks3.toList = true := all_parts.1.1.2.2

theorem output1_part4 :
    checkBlocks (outputByte 1) 60722 output1Blocks4.toList = true := all_parts.1.2.1.1

theorem output1_part5 :
    checkBlocks (outputByte 1) 83484 output1Blocks5.toList = true := all_parts.1.2.1.2

theorem output1_part6 :
    checkBlocks (outputByte 1) 108860 output1Blocks6.toList = true := all_parts.1.2.2.1

theorem output1_part7 :
    checkBlocks (outputByte 1) 133382 output1Blocks7.toList = true := all_parts.1.2.2.2

theorem output1_part8 :
    checkBlocks (outputByte 1) 148828 output1Blocks8.toList = true := all_parts.2.1.1.1

theorem output1_part9 :
    checkBlocks (outputByte 1) 162868 output1Blocks9.toList = true := all_parts.2.1.1.2

theorem output1_part10 :
    checkBlocks (outputByte 1) 175964 output1Blocks10.toList = true := all_parts.2.1.2.1

theorem output1_part11 :
    checkBlocks (outputByte 1) 189052 output1Blocks11.toList = true := all_parts.2.1.2.2

theorem output1_part12 :
    checkBlocks (outputByte 1) 204972 output1Blocks12.toList = true := all_parts.2.2.1.1

theorem output1_part13 :
    checkBlocks (outputByte 1) 220756 output1Blocks13.toList = true := all_parts.2.2.1.2

theorem output1_part14 :
    checkBlocks (outputByte 1) 235148 output1Blocks14.toList = true := all_parts.2.2.2.1

theorem output1_part15 :
    checkBlocks (outputByte 1) 248698 output1Blocks15.toList = true := all_parts.2.2.2.2

theorem output1_checks :
    checkBlocks (outputByte 1) 0 byteShiftColumn5.blocks.toList = true := by
  have joined : byteShiftColumn5.blocks = ((((output1Blocks0 ++ output1Blocks1) ++ (output1Blocks2 ++ output1Blocks3)) ++ ((output1Blocks4 ++ output1Blocks5) ++ (output1Blocks6 ++ output1Blocks7))) ++ (((output1Blocks8 ++ output1Blocks9) ++ (output1Blocks10 ++ output1Blocks11)) ++ ((output1Blocks12 ++ output1Blocks13) ++ (output1Blocks14 ++ output1Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output1_extent0, output1_extent1, output1_extent2, output1_extent3, output1_extent4, output1_extent5, output1_extent6, output1_extent7, output1_extent8, output1_extent9, output1_extent10, output1_extent11, output1_extent12, output1_extent13, output1_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output1_part0, output1_part1⟩, ⟨output1_part2, output1_part3⟩⟩, ⟨⟨output1_part4, output1_part5⟩, ⟨output1_part6, output1_part7⟩⟩⟩, ⟨⟨⟨output1_part8, output1_part9⟩, ⟨output1_part10, output1_part11⟩⟩, ⟨⟨output1_part12, output1_part13⟩, ⟨output1_part14, output1_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
