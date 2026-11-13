module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.AddSub.Batch000
public import Proven.Compiler.NativeExtension.AddSub.Batch001
public import Proven.Compiler.NativeExtension.AddSub.Batch002

@[expose] public section
namespace Airbender.Compiler.NativeExtension.AddSub
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.AddSub.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))

end Airbender.Compiler.NativeExtension.AddSub

namespace Airbender.Compiler.NativeExtension.AddSub
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.AddSubCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.AddSub.imported.circuit physical ∧
      PlacementAgreement Captures.AddSub.imported.circuit physical realized := by
  let values : Fin 48 → F := fun index => logical index.val
  let extended := FullArithmeticNative.AddSubCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.AddSubCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.AddSubCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.AddSub.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.AddSubCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.AddSub.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 48 := by kernel_rfl
    have unique : (Captures.AddSub.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.AddSub
