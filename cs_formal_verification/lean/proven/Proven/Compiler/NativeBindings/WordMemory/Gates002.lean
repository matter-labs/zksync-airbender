module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.WordMemory
public import Proven.GKRProtocol.CleanArithmeticNative.WordMemoryCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.WordMemory
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 32. -/
theorem gate32 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate32.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate32.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨32, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate32 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[2]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨2, by decide⟩))

/-- The actual native sparse relation supplies gate 33. -/
theorem gate33 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate33.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate33.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨33, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate33 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[3]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨3, by decide⟩))

/-- The actual native sparse relation supplies gate 34. -/
theorem gate34 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate34.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate34.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨34, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate34 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[4]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨4, by decide⟩))

/-- The actual native sparse relation supplies gate 35. -/
theorem gate35 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate35.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate35.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨35, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate35 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[8]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨8, by decide⟩))

/-- The actual native sparse relation supplies gate 36. -/
theorem gate36 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate36.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate36.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨36, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate36 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[15]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨15, by decide⟩))

/-- The actual native sparse relation supplies gate 37. -/
theorem gate37 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate37.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate37.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gatesChecked _ (List.get_mem _ ⟨37, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate37 (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.WordMemory.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[16]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨1, by decide⟩ ⟨16, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates002 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.WordMemory.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate32, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate33, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate34, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate35, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate36, Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate37], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank.address) = 0 :=
  (cons_holds (gate32 physical accepted) (cons_holds (gate33 physical accepted) (cons_holds (gate34 physical accepted) (cons_holds (gate35 physical accepted) (cons_holds (gate36 physical accepted) (cons_holds (gate37 physical accepted) (by intro gate member; cases member)))))))
end Airbender.Compiler.NativeBindings.WordMemory
