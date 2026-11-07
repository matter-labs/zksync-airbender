import Airbender.Proofs.GKRProtocol.PackedSetupSpans

namespace Tests.PackedSetupSpans
open Airbender.Compiler.PackedSetupEquality Airbender.Compiler.PackedSetupSpans
set_option warningAsError true

def requests : List Airbender.Compiler.PackedSetupSpans.Request := [
  ⟨.affine 6 1 1, [.affine 2 1 1, .affine 4 3 1]⟩,
  ⟨.periodic 5 0 (.literal 3 197121), [.periodic 2 0 (.linear 3 1), .periodic 3 0 (.literal 3 197121)]⟩,
  ⟨.affine 3 1 1, [.dense (.literal 3 197121)]⟩,
  ⟨.affine 6 1 1, [.dense (.append (.linear 3 1) (.linear 3 4))]⟩,
  ⟨.affine 4 3 0, [.dense (.constant 4 3)]⟩,
  ⟨.affine 6 0 1, [.dense (.range 6)]⟩,
  ⟨.affine 4 2 1, [.dense (.linear 4 2)]⟩,
  ⟨.periodic 2 0 (.range 4), [.dense (.range 1), .dense (.rotate 4 1), .dense (.linear 3 1)]⟩,
  ⟨.periodic 3 2 (.constant 2 1), [.dense (.linearRuns 6 1 2 2)]⟩,
  ⟨.periodic 3 1 (.constant 2 1), [.dense (.lookupRuns 6 2 (.linear 3 1))]⟩,
  ⟨.affine 4 1 1, [.dense (.packedBytes 4 67305985)]⟩,
  ⟨.affine 4 3 (-1), [.dense (.literal 4 66051)]⟩]

theorem checked : Airbender.Compiler.PackedSetupSpans.check requests = true := by decide +kernel

theorem original (index : Fin requests.length) :
    Airbender.Compiler.PackedSetupSpans.Fact (requests.get index) :=
  check_sound_at requests checked index

theorem wrong_value_rejected :
    Airbender.Compiler.PackedSetupSpans.check [⟨.affine 4 1 1, [.dense (.packedBytes 4 67305986)]⟩] = false := by decide +kernel

theorem missing_rows_rejected :
    Airbender.Compiler.PackedSetupSpans.check [⟨.affine 4 1 1, [.affine 3 1 1]⟩] = false := by decide +kernel

theorem source_bound_rejected : spanCheck (.affine 2 0 1) (.affine 3 0 1) 0 = false := by decide +kernel

theorem negative_value_rejected :
    Airbender.Compiler.PackedSetupSpans.check [⟨.affine 4 0 (-1), [.dense (.constant 4 0)]⟩] = false := by decide +kernel

end Tests.PackedSetupSpans
