module
public import Proven.Compiler.CPUWitnesses.SubwordMemory.Data
public import Proven.Compiler.CPUWitnesses.SubwordMemory.Fields000
public import Proven.Compiler.CPUWitnesses.SubwordMemory.Fields001
public import Proven.Compiler.NativeExtension.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.CPUWitnesses.SubwordMemory
open NativeArithmetic WorkerConstraints
set_option warningAsError true
set_option maxRecDepth 32768

/-- Every selector resolves to its retained primitive operand. -/
theorem resolved (group : Fin 3) :
    ((NativeLookups.selectorsFor (.pooled .subwordMemory)).filter (fun selector => selector.group == group)).mapM
      (NativeLookups.select (NativeLookups.circuitFor (.pooled .subwordMemory))) = .ok (operands group) := by
  fin_cases group <;> kernel_rfl

/-- Active rows retain all primitive query occurrences. -/
theorem enabled (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (active : logical 4 = 1) :
    ∀ group, ∀ value ∈ operands group, value.weight.value physical ≠ 0 := by
  intro group
  fin_cases group
  · exact (all_cons (enabled10 physical logical agreement active) (all_cons (enabled14 physical logical agreement active) (all_cons (enabled15 physical logical agreement active) (by intro value member; cases member))))
  · exact (all_cons (enabled0 physical logical agreement active) (all_cons (enabled1 physical logical agreement active) (all_cons (enabled2 physical logical agreement active) (all_cons (enabled11 physical logical agreement active) (all_cons (enabled12 physical logical agreement active) (by intro value member; cases member))))))
  · exact (all_cons (enabled3 physical logical agreement active) (all_cons (enabled4 physical logical agreement active) (all_cons (enabled5 physical logical agreement active) (all_cons (enabled6 physical logical agreement active) (all_cons (enabled7 physical logical agreement active) (all_cons (enabled8 physical logical agreement active) (all_cons (enabled9 physical logical agreement active) (all_cons (enabled13 physical logical agreement active) (by intro value member; cases member)))))))))

/-- Placement gives the same complete logical tuple at every resolved operand. -/
theorem fields (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical) (group : Fin 3) :
    (operands group).map (fun operand => operand.input.fields physical) = tuples logical group := by
  fin_cases group
  · exact (congrArg₂ List.cons (fields10 physical logical agreement) (congrArg₂ List.cons (fields14 physical logical agreement) (congrArg₂ List.cons (fields15 physical logical agreement) rfl)))
  · exact (congrArg₂ List.cons (fields0 physical logical agreement) (congrArg₂ List.cons (fields1 physical logical agreement) (congrArg₂ List.cons (fields2 physical logical agreement) (congrArg₂ List.cons (fields11 physical logical agreement) (congrArg₂ List.cons (fields12 physical logical agreement) rfl)))))
  · exact (congrArg₂ List.cons (fields3 physical logical agreement) (congrArg₂ List.cons (fields4 physical logical agreement) (congrArg₂ List.cons (fields5 physical logical agreement) (congrArg₂ List.cons (fields6 physical logical agreement) (congrArg₂ List.cons (fields7 physical logical agreement) (congrArg₂ List.cons (fields8 physical logical agreement) (congrArg₂ List.cons (fields9 physical logical agreement) (congrArg₂ List.cons (fields13 physical logical agreement) rfl))))))))

/-- Exact selector resolution and canonical tuple checks give the full native lookup argument. -/
noncomputable def arguments (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement Captures.SubwordMemory.imported.circuit physical logical)
    (active : logical 4 = 1) (checked : canonicalCheck initial program logical = true) :
    NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory)) (NativeLookups.selectorsFor (.pooled .subwordMemory))
      physical (NativePublicSetup.rows initial program (.pooled .subwordMemory)) :=
  CPUWitnesses.arguments_of_checked (tuples logical) (fun group =>
    (CPUWitnesses.requests_of_enabled physical group (operands group) (resolved group)
      (enabled physical logical agreement active group)).trans
      (congrArg Except.ok (fields physical logical agreement group))) checked

/-- The checked constructor describes this logical row exactly. -/
noncomputable def of_checked (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F)
    (sourceHolds : Satisfies FullArithmeticNative.SubwordMemoryCached.native.artifact.source
      (NativeExtension.SubwordMemory.inputValues logical))
    (checked : canonicalCheck initial program logical = true) (active : logical 4 = 1) :
    ProgramLogicalRowCertificate (NativePublicSetup.rows initial program) := by
  have extension := NativeExtension.SubwordMemory.extension_preserves logical sourceHolds
  let physical := Classical.choose extension
  have facts := Classical.choose_spec extension
  exact {
    row := ⟨.subwordMemory, logical⟩
    physical := physical
    arithmetic := facts.1
    placement := facts.2
    lookups := arguments initial program physical logical facts.2 active checked
    active := active }

/-- The constructor retains the complete supplied logical row. -/
theorem row_of_checked (initial : RV.State) (program : List Trace.RVMachineProgramEntry)
    (logical : Nat → F)
    (sourceHolds : Satisfies FullArithmeticNative.SubwordMemoryCached.native.artifact.source
      (NativeExtension.SubwordMemory.inputValues logical))
    (checked : canonicalCheck initial program logical = true) (active : logical 4 = 1) :
    (of_checked initial program logical sourceHolds checked active).row =
      (⟨.subwordMemory, logical⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := rfl

end Airbender.Compiler.CPUWitnesses.SubwordMemory
