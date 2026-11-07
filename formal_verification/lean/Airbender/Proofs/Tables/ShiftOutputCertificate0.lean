import Airbender.Proofs.Tables.ShiftOutputExtent0
import Airbender.Proofs.Tables.ShiftPackedEncoding.Column0

namespace Airbender.Verification.ShiftCertificate
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

private theorem all_parts :
    ((((checkBlocks (outputByte 0) 0 output0Blocks0.toList = true ∧ checkBlocks (outputByte 0) 26881 output0Blocks1.toList = true) ∧ (checkBlocks (outputByte 0) 51505 output0Blocks2.toList = true ∧ checkBlocks (outputByte 0) 74002 output0Blocks3.toList = true)) ∧ ((checkBlocks (outputByte 0) 89450 output0Blocks4.toList = true ∧ checkBlocks (outputByte 0) 104050 output0Blocks5.toList = true) ∧ (checkBlocks (outputByte 0) 118066 output0Blocks6.toList = true ∧ checkBlocks (outputByte 0) 132746 output0Blocks7.toList = true))) ∧ (((checkBlocks (outputByte 0) 149650 output0Blocks8.toList = true ∧ checkBlocks (outputByte 0) 164690 output0Blocks9.toList = true) ∧ (checkBlocks (outputByte 0) 178554 output0Blocks10.toList = true ∧ checkBlocks (outputByte 0) 192418 output0Blocks11.toList = true)) ∧ ((checkBlocks (outputByte 0) 208538 output0Blocks12.toList = true ∧ checkBlocks (outputByte 0) 222706 output0Blocks13.toList = true) ∧ (checkBlocks (outputByte 0) 236234 output0Blocks14.toList = true ∧ checkBlocks (outputByte 0) 249266 output0Blocks15.toList = true)))) := by
  have result := ShiftPackedEncoding.Lane0.native_checks
  have joined : byteShiftColumn4.blocks = ((((output0Blocks0 ++ output0Blocks1) ++ (output0Blocks2 ++ output0Blocks3)) ++ ((output0Blocks4 ++ output0Blocks5) ++ (output0Blocks6 ++ output0Blocks7))) ++ (((output0Blocks8 ++ output0Blocks9) ++ (output0Blocks10 ++ output0Blocks11)) ++ ((output0Blocks12 ++ output0Blocks13) ++ (output0Blocks14 ++ output0Blocks15)))) := rfl
  rw [joined] at result
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output0_extent0, output0_extent1, output0_extent2, output0_extent3, output0_extent4, output0_extent5, output0_extent6, output0_extent7, output0_extent8, output0_extent9, output0_extent10, output0_extent11, output0_extent12, output0_extent13, output0_extent14, Nat.reduceAdd] at result
  exact result

theorem output0_part0 :
    checkBlocks (outputByte 0) 0 output0Blocks0.toList = true := all_parts.1.1.1.1

theorem output0_part1 :
    checkBlocks (outputByte 0) 26881 output0Blocks1.toList = true := all_parts.1.1.1.2

theorem output0_part2 :
    checkBlocks (outputByte 0) 51505 output0Blocks2.toList = true := all_parts.1.1.2.1

theorem output0_part3 :
    checkBlocks (outputByte 0) 74002 output0Blocks3.toList = true := all_parts.1.1.2.2

theorem output0_part4 :
    checkBlocks (outputByte 0) 89450 output0Blocks4.toList = true := all_parts.1.2.1.1

theorem output0_part5 :
    checkBlocks (outputByte 0) 104050 output0Blocks5.toList = true := all_parts.1.2.1.2

theorem output0_part6 :
    checkBlocks (outputByte 0) 118066 output0Blocks6.toList = true := all_parts.1.2.2.1

theorem output0_part7 :
    checkBlocks (outputByte 0) 132746 output0Blocks7.toList = true := all_parts.1.2.2.2

theorem output0_part8 :
    checkBlocks (outputByte 0) 149650 output0Blocks8.toList = true := all_parts.2.1.1.1

theorem output0_part9 :
    checkBlocks (outputByte 0) 164690 output0Blocks9.toList = true := all_parts.2.1.1.2

theorem output0_part10 :
    checkBlocks (outputByte 0) 178554 output0Blocks10.toList = true := all_parts.2.1.2.1

theorem output0_part11 :
    checkBlocks (outputByte 0) 192418 output0Blocks11.toList = true := all_parts.2.1.2.2

theorem output0_part12 :
    checkBlocks (outputByte 0) 208538 output0Blocks12.toList = true := all_parts.2.2.1.1

theorem output0_part13 :
    checkBlocks (outputByte 0) 222706 output0Blocks13.toList = true := all_parts.2.2.1.2

theorem output0_part14 :
    checkBlocks (outputByte 0) 236234 output0Blocks14.toList = true := all_parts.2.2.2.1

theorem output0_part15 :
    checkBlocks (outputByte 0) 249266 output0Blocks15.toList = true := all_parts.2.2.2.2

theorem output0_checks :
    checkBlocks (outputByte 0) 0 byteShiftColumn4.blocks.toList = true := by
  have joined : byteShiftColumn4.blocks = ((((output0Blocks0 ++ output0Blocks1) ++ (output0Blocks2 ++ output0Blocks3)) ++ ((output0Blocks4 ++ output0Blocks5) ++ (output0Blocks6 ++ output0Blocks7))) ++ (((output0Blocks8 ++ output0Blocks9) ++ (output0Blocks10 ++ output0Blocks11)) ++ ((output0Blocks12 ++ output0Blocks13) ++ (output0Blocks14 ++ output0Blocks15)))) := rfl
  rw [joined]
  simp only [Array.toList_append, checkBlocks_append_iff,
    List.map_append, List.sum_append, Nat.zero_add,
    output0_extent0, output0_extent1, output0_extent2, output0_extent3, output0_extent4, output0_extent5, output0_extent6, output0_extent7, output0_extent8, output0_extent9, output0_extent10, output0_extent11, output0_extent12, output0_extent13, output0_extent14, Nat.reduceAdd]
  exact ⟨⟨⟨⟨output0_part0, output0_part1⟩, ⟨output0_part2, output0_part3⟩⟩, ⟨⟨output0_part4, output0_part5⟩, ⟨output0_part6, output0_part7⟩⟩⟩, ⟨⟨⟨output0_part8, output0_part9⟩, ⟨output0_part10, output0_part11⟩⟩, ⟨⟨output0_part12, output0_part13⟩, ⟨output0_part14, output0_part15⟩⟩⟩⟩

end Airbender.Verification.ShiftCertificate
