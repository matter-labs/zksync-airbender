module
public import Slop.Final.Circuits.Blake2G.Theorems
public import Slop.Blake2G.BlockFrame
public import Slop.Blake2G.NativeExecution
public import Slop.Blake2G.Soundness
public import Slop.Blake2G.Control
public import Slop.Blake2G.Addresses
public import Slop.Blake2G.State
public import Slop.Blake2G.Row
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Keccak.Permutation
public import Slop.Blake2G.CallGroups
public import Slop.Blake2G.PhysicalWords
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.ReverseFold
public import Human.Circuits.Blake2G.Memory

@[expose] public section

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
