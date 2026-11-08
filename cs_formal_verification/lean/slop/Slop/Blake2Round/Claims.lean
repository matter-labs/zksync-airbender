module
public import Slop.Blake2Round.NativeExecution
public import Slop.Blake2Round.Control
public import Slop.Blake2Round.Lookups
public import Slop.Blake2Round.Addresses
public import Slop.Blake2Round.Preparation
public import Slop.Blake2Round.Schedule
public import Slop.Blake2Round.Soundness
public import Slop.Blake2Round.Finalization
public import Slop.Blake2Round.PortAddresses
public import Slop.Blake2Round.Row
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Human.Trace.Workers.Keccak.Permutation
public import Slop.Blake2Round.Compression
public import Slop.Blake2Round.StateTransport
public import Slop.Delegation.NativeSegments
public import Slop.Delegation.ReverseFold

@[expose] public section

namespace Airbender.Blake2Round.Row


theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Row

namespace Airbender.Blake2Round.Control


theorem soundness {p : Nat} [Fact p.Prime] (hp : 8192 ≤ p)
    (setup : Table (ZMod p) (fields 6)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 6)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Control

namespace Airbender.Blake2Round.Preparation


theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (setup : Table (ZMod p) (fields 6)) :
    Properties.Soundness (circuitModel setup).relation spec := Proofs.soundness hp setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 6)) :
    Properties.Soundness (circuitModel setup).relation spec := soundness (by decide) setup

end Airbender.Blake2Round.Preparation

namespace Airbender.Blake2Round.Schedule


theorem soundness {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness setup

theorem babyBear_soundness (setup : Table (ZMod babyBearModulus) (fields 6)) :
    (circuitModel setup).SoundnessUnder InterfaceAssumptions spec := soundness setup

end Airbender.Blake2Round.Schedule

namespace Airbender.Blake2Round.Mixing


theorem soundness {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.mixing_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Mixing

namespace Airbender.Blake2Round.Finalization


theorem soundness {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p)
    (compatible : 64 * (-31457280 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder (InterfaceAssumptions (p := p)) spec :=
  Proofs.finalization_soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (InterfaceAssumptions (p := babyBearModulus)) spec := soundness (by decide) (by decide)


theorem nonfinal_soundness {p : Nat} [Fact p.Prime] :
    (circuitModel (p := p)).SoundnessUnder (NonFinalAssumptions (p := p)) spec :=
  Proofs.nonfinal_soundness

theorem babyBear_nonfinal_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder
      (NonFinalAssumptions (p := babyBearModulus)) spec := nonfinal_soundness

end Airbender.Blake2Round.Finalization

namespace Airbender.Blake2Round.Addresses


theorem soundness {p : Nat} [Fact p.Prime] (hp : 8388608 ≤ p)
    (compatible : 128 * (-15728640 : ZMod p) = 1) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := Proofs.soundness hp compatible

theorem babyBear_soundness :
    (circuitModel (p := babyBearModulus)).SoundnessUnder InterfaceAssumptions spec :=
  soundness (by decide) (by decide)

end Airbender.Blake2Round.Addresses

namespace Airbender.Blake2Round.Memory


end Airbender.Blake2Round.Memory

namespace Airbender.Blake2Round.Native


end Airbender.Blake2Round.Native
