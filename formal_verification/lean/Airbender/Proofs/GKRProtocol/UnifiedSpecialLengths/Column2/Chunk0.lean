import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part0
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part1
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part2
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part3
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part4
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part5
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part6
import Airbender.Proofs.GKRProtocol.UnifiedSpecialLengths.Column2.Chunk0Part7

namespace Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
open Airbender
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def lengthParts : List (List Setup.Block) := [part0, part1, part2, part3, part4, part5, part6, part7]

theorem sourceShape : Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0.original = lengthParts.flatten := by rfl

theorem originalLength : (Airbender.Compiler.UnifiedSpecialChunks.Column2.Chunk0.original.map Setup.Block.length).sum = 1920257 := by
  rw [sourceShape]
  simp only [lengthParts, List.flatten_cons, List.flatten_nil, List.map_append, List.sum_append, List.map_nil, List.sum_nil, partLength0, partLength1, partLength2, partLength3, partLength4, partLength5, partLength6, partLength7]; rfl

end Airbender.Compiler.UnifiedSpecialLengths.Column2.Chunk0
