module
public import Proven.Compiler.NativeInputPlacement
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

/-- Each native input names its captured logical column. -/
def inputLogicalIndices : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 218, 221, 224, 227, 230, 233, 236, 239, 242, 245, 248, 251, 254, 257, 260, 263, 266, 269, 272, 273, 274, 275, 216, 217, 219, 220, 222, 223, 225, 226, 228, 229, 231, 232, 234, 235, 237, 238, 240, 241, 243, 244, 246, 247, 249, 250, 252, 253, 255, 256, 258, 259, 261, 262, 264, 265, 267, 268, 270, 271]

/-- Read the source inputs in their actual native bank order. -/
noncomputable def inputValues (logical : Nat → F) (index : Fin 276) : F :=
  logical ((inputLogicalIndices[index.val]?).getD 0)

/-- The native extension retains the supplied values at every source placement. -/
theorem extension_preserves (logical : Nat → F)
    (holds : Satisfies FullArithmeticNative.BigintCached.native.artifact.source (inputValues logical)) :
    ∃ physical : GKRAddress → F, Holds Captures.Bigint.imported.circuit physical ∧
      PlacementAgreement Captures.Bigint.imported.circuit physical logical := by
  let values : Fin 276 → F := inputValues logical
  let extended := FullArithmeticNative.BigintCached.native.artifact.translation.extend values
  let physical := FullArithmeticNative.BigintCached.native.bank.materialize extended (fun _ => 0)
  have facts := FullArithmeticNative.BigintCached.native.full_arithmetic_extends values holds
  refine ⟨physical, native_holds physical ?_, ?_⟩
  · exact WireBank.materialize_gates _ FullArithmeticNative.BigintCached.native.bankRoundTrip extended
      (fun _ => 0) _ facts.2
  · apply NativePlacementWitness.agrees_with_reindexed_inputs
      FullArithmeticNative.BigintCached.native.inputs (by decide) inputLogicalIndices _ (by decide +kernel)
    intro index
    exact WireBank.materialize_source_input _ FullArithmeticNative.BigintCached.native.inputBank
      _ FullArithmeticNative.BigintCached.native.inputCoordinates FullArithmeticNative.BigintCached.native.bankRoundTrip
      values extended facts.1 (fun _ => 0) index

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
