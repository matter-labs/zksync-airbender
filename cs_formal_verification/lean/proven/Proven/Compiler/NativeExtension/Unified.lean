module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.Unified.Batch000
public import Proven.Compiler.NativeExtension.Unified.Batch001
public import Proven.Compiler.NativeExtension.Unified.Batch002
public import Proven.Compiler.NativeExtension.Unified.Batch003
public import Proven.Compiler.NativeExtension.Unified.Batch004
public import Proven.Compiler.NativeExtension.Unified.Batch005
public import Proven.Compiler.NativeExtension.Unified.Batch006
public import Proven.Compiler.NativeExtension.Unified.Batch007
public import Proven.Compiler.NativeExtension.Unified.Batch008

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Unified
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.UnifiedCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.Unified.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (append_zero (batch004 physical holds) (append_zero (batch005 physical holds) (append_zero (batch006 physical holds) (append_zero (batch007 physical holds) (append_zero (batch008 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))))))))

end Airbender.Compiler.NativeExtension.Unified

namespace Airbender.Compiler.NativeExtension.Unified
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.UnifiedCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.Unified.imported.circuit physical ∧
      PlacementAgreement Captures.Unified.imported.circuit physical realized := by
  let values : Fin 137 → F := fun index => logical index.val
  let extended := FullArithmeticNative.UnifiedCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.UnifiedCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.UnifiedCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.Unified.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.UnifiedCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.Unified.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 137 := by kernel_rfl
    have unique : (Captures.Unified.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.Unified
