import Airbender.Proofs.SubwordMemory.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

/-- RAM/ROM LB/LBU/LH/LHU and RAM SB/SH agree with native Sail: cell address, exact register
    or memory effects and PC+4. Input, decoder and native transport obligations
    are explicit in `InterfaceAssumptions`; merged writes preserve other bytes. -/
theorem soundness {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (program : Nat → BitVec 32) :
    (circuitModel (p := p) program).SoundnessUnder (InterfaceAssumptions program) spec :=
  Proofs.soundness hp inverse program

theorem babyBear_soundness (program : Nat → BitVec 32) :
    (circuitModel (p := babyBearModulus) program).SoundnessUnder (InterfaceAssumptions program) spec :=
  soundness (by decide) (by decide) program

end Airbender.SubwordMemory
