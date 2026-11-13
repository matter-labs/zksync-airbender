module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.ShiftBinop.Batch000
public import Proven.Compiler.NativeExtension.ShiftBinop.Batch001
public import Proven.Compiler.NativeExtension.ShiftBinop.Batch002
public import Proven.Compiler.NativeExtension.ShiftBinop.Batch003

@[expose] public section
namespace Airbender.Compiler.NativeExtension.ShiftBinop
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.ShiftBinopCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.ShiftBinop.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))

end Airbender.Compiler.NativeExtension.ShiftBinop

namespace Airbender.Compiler.NativeExtension.ShiftBinop
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.ShiftBinopCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.ShiftBinop.imported.circuit physical ∧
      PlacementAgreement Captures.ShiftBinop.imported.circuit physical realized := by
  let values : Fin 98 → F := fun index => logical index.val
  let extended := FullArithmeticNative.ShiftBinopCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.ShiftBinopCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.ShiftBinopCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.ShiftBinop.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.ShiftBinopCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.ShiftBinop.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 98 := by kernel_rfl
    have unique : (Captures.ShiftBinop.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.ShiftBinop
