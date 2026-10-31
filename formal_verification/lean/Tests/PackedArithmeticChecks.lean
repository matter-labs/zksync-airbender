import Airbender.Proofs.GKRProtocol.FullArithmeticChecks
import Mathlib.Data.ZMod.Basic

namespace Tests.PackedArithmeticChecks
open Airbender.Compiler
set_option warningAsError true

def identityArtifact : ArithmeticExtension 1 1 (ZMod 7) :=
  ⟨[atom 0], [.assertZero (.atom 0) (.atom 0)], id, atom⟩

def identityCertificate : Certificate identityArtifact.translation :=
  ⟨fun _ => [(constant 1, ⟨0, by decide⟩)], fun _ => [(constant 1, ⟨0, by decide⟩)]⟩

theorem identity_accepted :
    FullArithmeticChecks.check [.BaseLayerWitness 0] identityArtifact identityCertificate = true := by
  decide +kernel

theorem duplicate_address_rejected :
    FullArithmeticChecks.check [.BaseLayerWitness 0, .BaseLayerWitness 0]
      identityArtifact identityCertificate = false := by decide +kernel

theorem address_constructors_distinct :
    AddressUniqueChecks.check [.BaseLayerWitness 0, .BaseLayerMemory 0, .InnerLayer 0 0,
      .Cached 0 0, .Setup 0, .VirtualSetup .RangeCheck16Bits] = true := by decide +kernel

theorem missing_backward_rejected :
    FullArithmeticChecks.check [.BaseLayerWitness 0] identityArtifact
      { identityCertificate with backward := fun _ => [] } = false := by decide +kernel

theorem missing_forward_rejected :
    FullArithmeticChecks.check [.BaseLayerWitness 0] identityArtifact
      { identityCertificate with forward := fun _ => [] } = false := by decide +kernel

def changedGate : ArithmeticExtension 1 1 (ZMod 7) :=
  { identityArtifact with gates := [.assertZero (.atom 0) (.constant 1)] }

theorem changed_gate_rejected :
    FullArithmeticChecks.check [.BaseLayerWitness 0] changedGate
      ⟨fun _ => [(constant 1, ⟨0, by decide⟩)], fun _ => [(constant 1, ⟨0, by decide⟩)]⟩ = false := by decide +kernel

def changedProjection : ArithmeticExtension 1 1 (ZMod 7) :=
  { identityArtifact with extension := fun _ => constant 0 }

theorem changed_projection_rejected :
    FullArithmeticChecks.check [.BaseLayerWitness 0] changedProjection
      ⟨fun _ => [(constant 1, ⟨0, by decide⟩)], fun _ => [(constant 1, ⟨0, by decide⟩)]⟩ = false := by decide +kernel

end Tests.PackedArithmeticChecks
