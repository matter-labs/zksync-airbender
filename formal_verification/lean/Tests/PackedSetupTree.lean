import Airbender.Proofs.GKRProtocol.PackedSetupTree
import Airbender.Import.GKRProtocol.BlockCoverageImport

namespace Tests.PackedSetupTree
open Airbender.Compiler.PackedSetupEquality
set_option warningAsError true

private def exampleTree : CodeTree :=
  .branch 2 (.leaf [.affine 3 0 1, .dense (.literal 2 256)])
    (.leaf [.periodic 3 (-2) (.literal 2 256)])

theorem valid_metadata : exampleTree.valid = true := by decide +kernel
theorem changed_metadata_rejected :
    (CodeTree.branch 1 (.leaf [.affine 3 0 1, .dense (.literal 2 256)])
      (.leaf [.periodic 3 (-2) (.literal 2 256)])).valid = false := by decide +kernel
theorem complete_rows : checkTree exampleTree exampleTree [⟨0, 3, 11⟩] = true := by decide +kernel
theorem crossing_rows : checkTree exampleTree exampleTree [⟨1, 2, 8⟩] = true := by decide +kernel
theorem right_rows : checkTree exampleTree exampleTree [⟨2, 1, 6⟩] = true := by decide +kernel
theorem empty_rows : checkTree exampleTree exampleTree [⟨1, 0, 0⟩] = true := by decide +kernel
theorem clipped_rows : checkTree exampleTree exampleTree [⟨2, 4, 6⟩] = true := by decide +kernel
theorem past_end_rows : checkTree exampleTree exampleTree [⟨5, 2, 0⟩] = true := by decide +kernel
theorem wrong_rows_rejected : checkTree exampleTree exampleTree [⟨1, 2, 9⟩] = false := by decide +kernel
theorem changed_byte_rejected :
    checkTree (.leaf [.dense (.literal 2 256)]) (.leaf [.dense (.literal 2 257)]) [] = false := by decide +kernel
theorem changed_stride_rejected :
    checkTree (.leaf [.affine 3 0 (-1)]) (.leaf [.affine 3 0 1]) [] = false := by decide +kernel

theorem projection_rows :
    checkTreeWithChunks exampleTree exampleTree [⟨0, 2, 5⟩, ⟨2, 1, 6⟩] = true := by decide +kernel
theorem incomplete_leaf_rejected :
    checkTreeWithChunks exampleTree exampleTree [⟨0, 1, 3⟩] = false := by decide +kernel

private def viewTree : CodeTree :=
  .branch 1 (.leaf [.affine 3 0 1]) (.leaf [.affine 2 7 (-1)])
private def selected (first : Nat) : List Airbender.Setup.Block :=
  (viewTree.chunk first).map BlockCode.decode
private def firstPart : List Airbender.Setup.Block := selected 0
private def secondPart : List Airbender.Setup.Block := selected 1
private def viewColumn : Airbender.Setup.Column :=
  ⟨[.affine 3 0 1, .affine 2 7 (-1)].toArray⟩

open Airbender.Compiler.BlockCoverageImport
column_parts_cover application_view_binding from viewColumn parts [firstPart, secondPart]

end Tests.PackedSetupTree
