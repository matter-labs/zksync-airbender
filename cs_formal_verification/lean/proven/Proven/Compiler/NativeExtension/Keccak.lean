module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.Keccak.Batch000
public import Proven.Compiler.NativeExtension.Keccak.Batch001
public import Proven.Compiler.NativeExtension.Keccak.Batch002
public import Proven.Compiler.NativeExtension.Keccak.Batch003
public import Proven.Compiler.NativeExtension.Keccak.Batch004
public import Proven.Compiler.NativeExtension.Keccak.Batch005
public import Proven.Compiler.NativeExtension.Keccak.Batch006
public import Proven.Compiler.NativeExtension.Keccak.Batch007
public import Proven.Compiler.NativeExtension.Keccak.Batch008
public import Proven.Compiler.NativeExtension.Keccak.Batch009
public import Proven.Compiler.NativeExtension.Keccak.Batch010
public import Proven.Compiler.NativeExtension.Keccak.Batch011
public import Proven.Compiler.NativeExtension.Keccak.Batch012
public import Proven.Compiler.NativeExtension.Keccak.Batch013

@[expose] public section
namespace Airbender.Compiler.NativeExtension.Keccak
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (append_zero (batch004 physical holds) (append_zero (batch005 physical holds) (append_zero (batch006 physical holds) (append_zero (batch007 physical holds) (append_zero (batch008 physical holds) (append_zero (batch009 physical holds) (append_zero (batch010 physical holds) (append_zero (batch011 physical holds) (append_zero (batch012 physical holds) (append_zero (batch013 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))

end Airbender.Compiler.NativeExtension.Keccak

namespace Airbender.Compiler.NativeExtension.Keccak
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.KeccakCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.Keccak.imported.circuit physical ∧
      PlacementAgreement Captures.Keccak.imported.circuit physical realized := by
  let values : Fin 266 → F := fun index => logical index.val
  let extended := FullArithmeticNative.KeccakCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.KeccakCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.KeccakCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.Keccak.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.KeccakCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.Keccak.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 266 := by kernel_rfl
    have unique : (Captures.Keccak.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.Keccak
