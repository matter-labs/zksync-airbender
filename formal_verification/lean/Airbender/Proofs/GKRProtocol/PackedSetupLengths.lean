import Airbender.Proofs.GKRProtocol.PackedSetupEquality

namespace Airbender.Compiler.PackedSetupLengths
open Airbender.Setup PackedSetupEquality
set_option warningAsError true

structure Request where
  blocks : List BlockCode
  expected : Nat

def check (requests : List Request) : Bool :=
  requests.all fun request => (request.blocks.map BlockCode.length).sum == request.expected

def Fact (request : Request) : Prop :=
  ((request.blocks.map BlockCode.decode).map Block.length).sum = request.expected

theorem check_sound (requests : List Request) (checked : check requests = true)
    (request : Request) (member : request ∈ requests) : Fact request := by
  have rows := beq_iff_eq.mp (List.all_eq_true.mp checked request member)
  simpa only [Fact, List.map_map, Function.comp_def, BlockCode.decode_length] using rows

theorem check_sound_at (requests : List Request) (checked : check requests = true)
    (index : Fin requests.length) : Fact (requests.get index) :=
  check_sound requests checked _ (List.get_mem requests index)

end Airbender.Compiler.PackedSetupLengths
