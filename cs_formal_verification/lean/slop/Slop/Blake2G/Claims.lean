import Slop.Final.Circuits.Blake2G.Theorems
import Slop.Blake2G.BlockFrame
import Slop.Blake2G.NativeExecution
import Slop.Blake2G.Soundness
import Slop.Blake2G.Control
import Slop.Blake2G.Addresses
import Slop.Blake2G.State
import Slop.Blake2G.Row
import Human.Helpers.Delegation.SpanABI
import Human.Trace.Workers.Blake2G.WorkVector
import Human.Trace.Workers.Keccak.Permutation
import Slop.Blake2G.CallGroups
import Slop.Blake2G.PhysicalWords
import Slop.Delegation.NativeSegments
import Slop.Delegation.ReverseFold
import Human.Circuits.Blake2G.Memory

namespace Airbender.Blake2G


namespace Row


theorem soundness {p : Nat} [Fact p.Prime] (hp : 33554432 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Row

namespace Control


theorem soundness {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) :
    Properties.Soundness (circuitModel (p := p)).relation spec :=
  Proofs.soundness hp

theorem babyBear_soundness :
    Properties.Soundness (circuitModel (p := babyBearModulus)).relation spec :=
  soundness (by decide)

end Control

namespace Addresses


theorem soundness {p : Nat} [Fact p.Prime] (hp : 33554432 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Addresses

namespace State


theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec :=
  Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end State

namespace Memory


end Memory

end Airbender.Blake2G

namespace Airbender.Blake2G.Native

end Airbender.Blake2G.Native
