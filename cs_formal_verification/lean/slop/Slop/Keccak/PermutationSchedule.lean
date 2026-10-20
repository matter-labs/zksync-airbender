import Slop.Keccak.PhysicalStep
import Slop.Keccak.DeferredIota

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

def logicalLanes (round : Nat) (state : LaneState) : Vector Nat 25 :=
  Vector.ofFn fun lane => state ⟨Controller.physicalLane round lane,
    Nat.lt_trans (Controller.Proofs.physical_bound round lane) (by decide)⟩

end Airbender.Keccak.Proofs
