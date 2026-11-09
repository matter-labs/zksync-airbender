import Airbender.Review.Trace.Families.ReducedMachine.InitializationComponent
import Airbender.Review.Circuits.ReducedMachine.MainDecoder

namespace Airbender.NativeInactiveGlobal
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Pack the existing shared main and its actual scalar/decoder observations.
    This constructs observations only; no global acceptance is asserted. -/
noncomputable def packed {R : Type} [Field R] (gamma : R)
    (proof : Airbender.ReducedMachine.NativeDecoderTableArguments.Proof R)
    (base : Nat → BaseAuxiliaryColumn → F) (witness : Nat → Scalar16WitnessColumn → F)
    (setup : Nat → Scalar16SetupColumn → F) (polynomial : Polynomial R) (omega : R) :
    NativeMainDecoder.Proof R :=
  let scalar := NativeScalarTableCompletion.scalarView gamma proof.main base witness setup polynomial omega
  ⟨⟨proof.main,scalar.initialization.base,scalar.witness,scalar.setup,polynomial,omega,
      NativeInitializationComponent.observedValues scalar⟩,
    proof.witness,proof.setup,proof.polynomial,proof.omega⟩

/-- Every position of this u32-indexed batch is the SAME constructed component.
    Duplicate positions and every ordinary request remain. No small-batch filter. -/
def copies {R : Type} [Field R] (proof : NativeMainDecoder.Proof R) (count : BitVec 32) : NativeMainDecoder.Batch R :=
  ⟨count,Vector.replicate count.toNat proof⟩
end Airbender.NativeInactiveGlobal
