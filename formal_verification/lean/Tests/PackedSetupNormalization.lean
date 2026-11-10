import Airbender.Proofs.GKRProtocol.PackedSetupNormalization

namespace Tests.PackedSetupNormalization
open Airbender.Compiler.PackedSetupEquality Airbender.Compiler.PackedSetupNormalization
set_option warningAsError true

def requests : List Request := [
  ⟨[.affine 2 5 3, .affine 3 11 3], [.affine 5 5 3], 5⟩,
  ⟨[.periodic 2 0 (.constant 1 3), .periodic 3 0 (.linear 1 3)],
    [.periodic 5 0 (.constant 1 3)], 5⟩,
  ⟨[.periodic 2 0 (.constant 1 3), .periodic 3 0 (.constant 1 4)],
    [.periodic 2 0 (.constant 1 3), .periodic 3 0 (.constant 1 4)], 5⟩]

theorem checked : check requests = true := by decide +kernel

theorem original (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound_at requests checked index

theorem wrong_value_rejected :
    check [⟨[.affine 2 5 3, .affine 3 12 3], [.affine 5 5 3], 5⟩] = false := by decide +kernel

theorem wrong_length_rejected :
    check [⟨[.affine 2 5 3, .affine 3 11 3], [.affine 5 5 3], 6⟩] = false := by decide +kernel

end Tests.PackedSetupNormalization
