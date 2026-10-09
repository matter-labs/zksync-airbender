import Airbender.Proofs.SubwordMemory.Soundness
import Airbender.Proofs.BabyBear

namespace Airbender.SubwordMemory
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- RAM/ROM LB/LBU/LH/LHU and RAM SB/SH agree with native Sail: cell address, exact register
    or memory effects and PC+4. Input, decoder and native transport obligations
    are explicit in `RowInterfaces`; merged writes preserve other bytes. -/
theorem row_soundness {p : Nat} [Fact p.Prime] (hp : 33554432 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) (program : Nat → BitVec 32) :
    (rowCircuitModel (p := p) program).SoundnessUnder (RowInterfaces program) spec :=
  Proofs.soundness hp inverse program

theorem babyBear_row_soundness (program : Nat → BitVec 32) :
    (rowCircuitModel (p := babyBearModulus) program).SoundnessUnder (RowInterfaces program) spec :=
  row_soundness (by decide) (by decide) program

end Airbender.SubwordMemory
