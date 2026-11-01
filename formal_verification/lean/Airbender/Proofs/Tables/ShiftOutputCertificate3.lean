import Airbender.Proofs.Tables.ShiftOutputExtent3
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column3

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

private theorem all_parts :
    ((((checkBlocks (outputByte 3) 0 output3Blocks0.toList = true ∧ checkBlocks (outputByte 3) 16537 output3Blocks1.toList = true) ∧ (checkBlocks (outputByte 3) 30633 output3Blocks2.toList = true ∧ checkBlocks (outputByte 3) 43945 output3Blocks3.toList = true)) ∧ ((checkBlocks (outputByte 3) 57033 output3Blocks4.toList = true ∧ checkBlocks (outputByte 3) 72585 output3Blocks5.toList = true) ∧ (checkBlocks (outputByte 3) 88497 output3Blocks6.toList = true ∧ checkBlocks (outputByte 3) 103321 output3Blocks7.toList = true))) ∧ (((checkBlocks (outputByte 3) 117401 output3Blocks8.toList = true ∧ checkBlocks (outputByte 3) 131937 output3Blocks9.toList = true) ∧ (checkBlocks (outputByte 3) 149105 output3Blocks10.toList = true ∧ checkBlocks (outputByte 3) 164377 output3Blocks11.toList = true)) ∧ ((checkBlocks (outputByte 3) 178449 output3Blocks12.toList = true ∧ checkBlocks (outputByte 3) 192377 output3Blocks13.toList = true) ∧ (checkBlocks (outputByte 3) 216065 output3Blocks14.toList = true ∧ checkBlocks (outputByte 3) 240153 output3Blocks15.toList = true)))) := by
  have result := ShiftPackedEncoding.Lane3.native_checks
  have joined : byteShiftColumn7.blocks = ((((output3Blocks0 ++ output3Blocks1) ++ (output3Blocks2 ++ output3Blocks3)) ++ ((output3Blocks4 ++ output3Blocks5) ++ (output3Blocks6 ++ output3Blocks7))) ++ (((output3Blocks8 ++ output3Blocks9) ++ (output3Blocks10 ++ output3Blocks11)) ++ ((output3Blocks12 ++ output3Blocks13) ++ (output3Blocks14 ++ output3Blocks15)))) := rfl
  rw [joined] at result
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output3_extent0, output3_extent1, output3_extent2, output3_extent3, output3_extent4, output3_extent5, output3_extent6, output3_extent7, output3_extent8, output3_extent9, output3_extent10, output3_extent11, output3_extent12, output3_extent13, output3_extent14, Nat.reduceAdd] at result
  exact result

theorem output3_part0 :
    checkBlocks (outputByte 3) 0 output3Blocks0.toList = true := all_parts.1.1.1.1

theorem output3_part1 :
    checkBlocks (outputByte 3) 16537 output3Blocks1.toList = true := all_parts.1.1.1.2

theorem output3_part2 :
    checkBlocks (outputByte 3) 30633 output3Blocks2.toList = true := all_parts.1.1.2.1

theorem output3_part3 :
    checkBlocks (outputByte 3) 43945 output3Blocks3.toList = true := all_parts.1.1.2.2

theorem output3_part4 :
    checkBlocks (outputByte 3) 57033 output3Blocks4.toList = true := all_parts.1.2.1.1

theorem output3_part5 :
    checkBlocks (outputByte 3) 72585 output3Blocks5.toList = true := all_parts.1.2.1.2

theorem output3_part6 :
    checkBlocks (outputByte 3) 88497 output3Blocks6.toList = true := all_parts.1.2.2.1

theorem output3_part7 :
    checkBlocks (outputByte 3) 103321 output3Blocks7.toList = true := all_parts.1.2.2.2

theorem output3_part8 :
    checkBlocks (outputByte 3) 117401 output3Blocks8.toList = true := all_parts.2.1.1.1

theorem output3_part9 :
    checkBlocks (outputByte 3) 131937 output3Blocks9.toList = true := all_parts.2.1.1.2

theorem output3_part10 :
    checkBlocks (outputByte 3) 149105 output3Blocks10.toList = true := all_parts.2.1.2.1

theorem output3_part11 :
    checkBlocks (outputByte 3) 164377 output3Blocks11.toList = true := all_parts.2.1.2.2

theorem output3_part12 :
    checkBlocks (outputByte 3) 178449 output3Blocks12.toList = true := all_parts.2.2.1.1

theorem output3_part13 :
    checkBlocks (outputByte 3) 192377 output3Blocks13.toList = true := all_parts.2.2.1.2

theorem output3_part14 :
    checkBlocks (outputByte 3) 216065 output3Blocks14.toList = true := all_parts.2.2.2.1

theorem output3_part15 :
    checkBlocks (outputByte 3) 240153 output3Blocks15.toList = true := all_parts.2.2.2.2

theorem output3_checks :
    checkBlocks (outputByte 3) 0 byteShiftColumn7.blocks.toList = true := by
  have joined : byteShiftColumn7.blocks = ((((output3Blocks0 ++ output3Blocks1) ++ (output3Blocks2 ++ output3Blocks3)) ++ ((output3Blocks4 ++ output3Blocks5) ++ (output3Blocks6 ++ output3Blocks7))) ++ (((output3Blocks8 ++ output3Blocks9) ++ (output3Blocks10 ++ output3Blocks11)) ++ ((output3Blocks12 ++ output3Blocks13) ++ (output3Blocks14 ++ output3Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output3_extent0, output3_extent1, output3_extent2, output3_extent3, output3_extent4, output3_extent5, output3_extent6, output3_extent7, output3_extent8, output3_extent9, output3_extent10, output3_extent11, output3_extent12, output3_extent13, output3_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output3_part0, output3_part1⟩, ⟨output3_part2, output3_part3⟩⟩, ⟨⟨output3_part4, output3_part5⟩, ⟨output3_part6, output3_part7⟩⟩⟩, ⟨⟨⟨output3_part8, output3_part9⟩, ⟨output3_part10, output3_part11⟩⟩, ⟨⟨output3_part12, output3_part13⟩, ⟨output3_part14, output3_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
