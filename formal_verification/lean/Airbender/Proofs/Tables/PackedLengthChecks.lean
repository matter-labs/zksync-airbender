import Airbender.Proofs.Tables.PackedWordColumn

namespace Airbender.Verification.PackedLengthChecks
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks PackedWordColumn
set_option warningAsError true

structure Request where
  blocks : List Code
  expected : Nat

def check (requests : List Request) : Bool :=
  requests.all fun request => codeLength request.blocks == request.expected

theorem check_sound (requests : List Request) (checked : check requests = true) :
    ∀ request ∈ requests,
      ((request.blocks.map (Code.decode 65536)).map Block.length).sum = request.expected := by
  intro request member
  rw [decoded_length]
  exact beq_iff_eq.mp (List.all_eq_true.mp checked request member)

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) :
    (((requests.get index).blocks.map (Code.decode 65536)).map Block.length).sum =
      (requests.get index).expected :=
  check_sound requests checked _ (List.get_mem requests index)

end Airbender.Verification.PackedLengthChecks
