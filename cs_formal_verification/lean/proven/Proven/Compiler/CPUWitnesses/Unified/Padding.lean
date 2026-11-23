module
public import Proven.Compiler.CPUWitnesses.Unified
public import Proven.Compiler.CPUWitnesses.Padding

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.Unified
open NativeArithmetic
set_option warningAsError true
set_option maxRecDepth 32768

/-- A padding row keeps every query except the decoder query, which its execute mask disables. -/
noncomputable def paddingTuples (logical : Nat → F) (group : Fin 3) : List (List F) :=
  if group = 0 then (tuples logical group).drop 1 else tuples logical group

/-- The native requests of a padding row are all its tuples except the decoder tuple. -/
theorem padding_requests (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.Unified.imported.circuit physical logical)
    (padding : logical 4 = 0) (group : Fin 3) :
    NativeLookups.requests (NativeLookups.circuitFor .unified) (NativeLookups.selectorsFor .unified)
      physical group = .ok (paddingTuples logical group) := by
  have unmasked : ∀ value ∈ (operands 0).drop 1 ++ operands 1 ++ operands 2, value.weight = .one := by
    intro value member
    simp only [operands, List.get, List.drop, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have enabled (value : NativeLookups.Operand) (member : value ∈ (operands 0).drop 1 ++ operands 1 ++ operands 2) :
      value.weight.value physical ≠ 0 := by
    rw [unmasked value member]
    exact one_ne_zero
  fin_cases group
  · have placed : physical (.BaseLayerMemory 21) = logical 4 :=
      WorkerConstraints.placed agreement (position := 4) (by kernel_rfl)
    refine (CPUWitnesses.requests_of_masked_head physical 0 operand18 ((operands 0).drop 1) (resolved 0) ?_ ?_).trans
      (congrArg Except.ok ((congrArg (List.drop 1) (fields physical logical agreement 0)).trans rfl))
    · change physical (.BaseLayerMemory 21) = 0
      rw [placed, padding]
    · intro value member
      exact enabled value (List.mem_append_left _ (List.mem_append_left _ member))
  · refine (CPUWitnesses.requests_of_enabled physical 1 (operands 1) (resolved 1) ?_).trans
      (congrArg Except.ok ((fields physical logical agreement 1).trans rfl))
    intro value member
    exact enabled value (List.mem_append_left _ (List.mem_append_right _ member))
  · refine (CPUWitnesses.requests_of_enabled physical 2 (operands 2) (resolved 2) ?_).trans
      (congrArg Except.ok ((fields physical logical agreement 2).trans rfl))
    intro value member
    exact enabled value (List.mem_append_right _ member)

/-- A checked padding row supplies native gates, placement and public lookups with execute zero. -/
noncomputable def padding_of_checked (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F)
    (sourceHolds : Satisfies FullArithmeticNative.UnifiedCached.native.artifact.source
      (NativeExtension.Unified.inputValues logical))
    (checked : CPUWitnesses.canonicalCheck .unified initial program (paddingTuples logical) = true)
    (padding : logical 4 = 0) :
    UnifiedRowCertificate (NativePublicSetup.rows initial program) := by
  have extension := NativeExtension.Unified.extension_preserves logical sourceHolds
  let physical := Classical.choose extension
  have facts := Classical.choose_spec extension
  exact {
    row := ⟨.machine, logical⟩
    physical := physical
    arithmetic := facts.1
    placement := facts.2
    lookups := CPUWitnesses.arguments_of_checked (paddingTuples logical)
      (padding_requests physical logical facts.2 padding) checked }

end Airbender.Compiler.CPUWitnesses.Unified
