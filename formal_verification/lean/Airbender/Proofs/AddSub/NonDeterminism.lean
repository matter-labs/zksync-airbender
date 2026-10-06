import Airbender.Review.AddSub.NonDeterminism
import Airbender.Proofs.AddSub.PC
import Airbender.Proofs.Sail.PC

namespace Airbender.AddSub.Proofs

theorem nondeterminism_write_soundness {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1) :
    (NonDeterminism.writeModel (p := p)).SoundnessUnder
      NonDeterminism.WriteInterfaces NonDeterminism.writeSpec := by
  rintro input finalPC w ⟨interfaces, constraints, mapping, _⟩
  obtain ⟨_, _, pc⟩ := pc_successor hp inverse constraints mapping interfaces.initialPCBounds
  exact Reference.RiscV.Sail.retire_no_write interfaces.pcRead pc

end Airbender.AddSub.Proofs
