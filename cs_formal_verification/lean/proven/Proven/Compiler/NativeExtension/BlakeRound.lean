module
public import Proven.Compiler.PlacementWitness
public import Proven.Compiler.NativeExtension.BlakeRound.Batch000
public import Proven.Compiler.NativeExtension.BlakeRound.Batch001
public import Proven.Compiler.NativeExtension.BlakeRound.Batch002
public import Proven.Compiler.NativeExtension.BlakeRound.Batch003
public import Proven.Compiler.NativeExtension.BlakeRound.Batch004
public import Proven.Compiler.NativeExtension.BlakeRound.Batch005
public import Proven.Compiler.NativeExtension.BlakeRound.Batch006
public import Proven.Compiler.NativeExtension.BlakeRound.Batch007
public import Proven.Compiler.NativeExtension.BlakeRound.Batch008
public import Proven.Compiler.NativeExtension.BlakeRound.Batch009
public import Proven.Compiler.NativeExtension.BlakeRound.Batch010
public import Proven.Compiler.NativeExtension.BlakeRound.Batch011
public import Proven.Compiler.NativeExtension.BlakeRound.Batch012
public import Proven.Compiler.NativeExtension.BlakeRound.Batch013
public import Proven.Compiler.NativeExtension.BlakeRound.Batch014
public import Proven.Compiler.NativeExtension.BlakeRound.Batch015
public import Proven.Compiler.NativeExtension.BlakeRound.Batch016
public import Proven.Compiler.NativeExtension.BlakeRound.Batch017
public import Proven.Compiler.NativeExtension.BlakeRound.Batch018
public import Proven.Compiler.NativeExtension.BlakeRound.Batch019

@[expose] public section
namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.BlakeRound.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (append_zero (batch003 physical holds) (append_zero (batch004 physical holds) (append_zero (batch005 physical holds) (append_zero (batch006 physical holds) (append_zero (batch007 physical holds) (append_zero (batch008 physical holds) (append_zero (batch009 physical holds) (append_zero (batch010 physical holds) (append_zero (batch011 physical holds) (append_zero (batch012 physical holds) (append_zero (batch013 physical holds) (append_zero (batch014 physical holds) (append_zero (batch015 physical holds) (append_zero (batch016 physical holds) (append_zero (batch017 physical holds) (append_zero (batch018 physical holds) (append_zero (batch019 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member)))))))))))))))))))))

end Airbender.Compiler.NativeExtension.BlakeRound

namespace Airbender.Compiler.NativeExtension.BlakeRound
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.BlakeRoundCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.BlakeRound.imported.circuit physical ∧
      PlacementAgreement Captures.BlakeRound.imported.circuit physical realized := by
  let values : Fin 763 → F := fun index => logical index.val
  let extended := FullArithmeticNative.BlakeRoundCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.BlakeRoundCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.BlakeRoundCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.BlakeRound.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.BlakeRoundCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.BlakeRound.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 763 := by kernel_rfl
    have unique : (Captures.BlakeRound.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)

end Airbender.Compiler.NativeExtension.BlakeRound
