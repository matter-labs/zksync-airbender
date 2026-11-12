module
public import Proven.InitsTeardowns.Native.Standalone
public import Proven.InitsTeardowns.Native.Unified

@[expose] public section
namespace Airbender.InitsTeardowns.Native

/-- The native memory-product graph is bound to the imported artifact. -/
theorem standalone_binding : StandaloneBindingClaim := Proofs.Standalone.binding

/-- Every accepted gate computes the complete native token products. -/
theorem standalone_soundness : StandaloneSoundnessClaim := Proofs.Standalone.soundness

/-- The native gate premises admit an assignment. -/
theorem standalone_satisfiable : StandaloneSatisfiableClaim := Proofs.Standalone.satisfiable

/-- The native memory-product graph is bound to the imported artifact. -/
theorem unified_binding : UnifiedBindingClaim := Proofs.Unified.binding

/-- Every accepted gate computes the complete native token products. -/
theorem unified_soundness : UnifiedSoundnessClaim := Proofs.Unified.soundness

/-- The native gate premises admit an assignment. -/
theorem unified_satisfiable : UnifiedSatisfiableClaim := Proofs.Unified.satisfiable

end Airbender.InitsTeardowns.Native
