module
public import Proven.Compiler.NativeInputPlacement
public import Proven.Compiler.NativeExtension.JumpBranch.Batch000
public import Proven.Compiler.NativeExtension.JumpBranch.Batch001
public import Proven.Compiler.NativeExtension.JumpBranch.Batch002

@[expose] public section
namespace Airbender.Compiler.NativeExtension.JumpBranch
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option warningAsError true
set_option maxRecDepth 65536

/-- The source extension satisfies every actual cached scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.JumpBranchCached.native.bank.address) = 0) :
    Holds Airbender.Compiler.Captures.JumpBranch.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (batch000 physical holds) (append_zero (batch001 physical holds) (append_zero (batch002 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))

end Airbender.Compiler.NativeExtension.JumpBranch

namespace Airbender.Compiler.NativeExtension.JumpBranch
open Airbender Airbender.Compiler NativeArithmetic
set_option maxRecDepth 65536

/-- Each native input names its captured logical column. -/
def inputLogicalIndices : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]

/-- Read the source inputs in their actual native bank order. -/
noncomputable def inputValues (logical : Nat → F) (index : Fin 55) : F :=
  logical ((inputLogicalIndices[index.val]?).getD 0)

/-- The native extension retains the supplied values at every source placement. -/
theorem extension_preserves (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.JumpBranchCached.native.artifact.source (inputValues logical)) :
    ∃ physical : GKRAddress → F, Holds Captures.JumpBranch.imported.circuit physical ∧
      PlacementAgreement Captures.JumpBranch.imported.circuit physical logical := by
  let values : Fin 55 → F := inputValues logical
  let extended := FullArithmeticNative.JumpBranchCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.JumpBranchCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.JumpBranchCached.native.full_arithmetic_extends values holds
  refine ⟨physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.JumpBranchCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · apply NativePlacementWitness.agrees_with_reindexed_inputs
      FullArithmeticNative.JumpBranchCached.native.inputs (by decide) inputLogicalIndices _ (by decide +kernel)
    intro index
    exact WireBank.materialize_source_input _ FullArithmeticNative.JumpBranchCached.native.inputBank
      _ FullArithmeticNative.JumpBranchCached.native.inputCoordinates FullArithmeticNative.JumpBranchCached.native.bankRoundTrip
      values extended facts.1 (fun _ => 0) index

theorem extension (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.JumpBranchCached.native.artifact.source
      (fun index => logical index.val)) :
    ∃ (physical : GKRAddress → F) (realized : Nat → F), Holds Captures.JumpBranch.imported.circuit physical ∧
      PlacementAgreement Captures.JumpBranch.imported.circuit physical realized := by
  let values : Fin 55 → F := fun index => logical index.val
  let extended := FullArithmeticNative.JumpBranchCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.JumpBranchCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.JumpBranchCached.native.full_arithmetic_extends values holds
  refine ⟨physical, NativePlacementWitness.assignment Captures.JumpBranch.imported.circuit.placement_data.entries.toList physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.JumpBranchCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · have keys : Captures.JumpBranch.imported.circuit.placement_data.entries.toList.map Prod.fst =
        List.range 55 := by kernel_rfl
    have unique : (Captures.JumpBranch.imported.circuit.placement_data.entries.toList.map Prod.fst).Nodup := by
      rw [keys]
      exact List.nodup_range
    intro entry member
    exact NativePlacementWitness.agrees _ unique physical entry (by simpa using member)


end Airbender.Compiler.NativeExtension.JumpBranch
