module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.Bigint.Batch000
public import Proven.Compiler.NativeExtension.Bigint.Batch001
public import Proven.Compiler.NativeExtension.Bigint.Batch002
public import Proven.Compiler.NativeExtension.Bigint.Batch003
public import Proven.Compiler.NativeExtension.Bigint.Batch004
public import Proven.Compiler.NativeExtension.Bigint.Batch005
public import Proven.Compiler.NativeExtension.Bigint.Batch006
public import Proven.Compiler.NativeExtension.Bigint.Batch007
public import Proven.Compiler.NativeExtension.Bigint.Batch008
public import Proven.Compiler.NativeExtension.Bigint.Batch009
public import Proven.Compiler.NativeExtension.Bigint.Batch010
public import Proven.Compiler.NativeExtension.Bigint.Batch011

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Bigint
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BigintCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.Bigint.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (append_zero (batch004 physical holds) (append_zero (batch005 physical holds) (append_zero (batch006 physical holds) (append_zero (batch007 physical holds) (append_zero (batch008 physical holds) (append_zero (batch009 physical holds) (append_zero (batch010 physical holds) (append_zero (batch011 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))

end Airbender.Compiler.NativeExtension.Bigint

namespace Airbender.Compiler.NativeExtension.Bigint
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.BigintCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.Bigint.imported.circuit physical ∧
      PlacementAgreement Captures.Bigint.imported.circuit physical realized := by
  let values : Fin 276 → F := fun index => logical index.val
  let extended := FullArithmeticNative.BigintCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.BigintCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.BigintCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.Bigint.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.BigintCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.Bigint.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 276 := by kernel_rfl
    have unique : (Captures.Bigint.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.Bigint
