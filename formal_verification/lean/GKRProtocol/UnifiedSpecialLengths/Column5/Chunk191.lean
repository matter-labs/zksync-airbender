import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part0
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part1
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part2
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part3
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part4
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part5
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part6
import GKRProtocol.UnifiedSpecialLengths.Column5.Chunk191Part7

namespace Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def lengthParts : List (List Setup.Block) := [part0, part1, part2, part3, part4, part5, part6, part7]

theorem sourceShape : Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191.original = lengthParts.flatten := by rfl

theorem originalLength : (Airbender.Compiler.UnifiedSpecialChunks.Column5.Chunk191.original.map Setup.Block.length).sum = 1184588 := by
  rw [sourceShape]
  simp only [lengthParts, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, partLength0, partLength1, partLength2, partLength3, partLength4, partLength5, partLength6, partLength7]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column5.Chunk191
