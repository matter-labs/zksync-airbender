module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- The actual native sparse relation supplies gate 144. -/
theorem gate144 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate144.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate144.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨144, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate144 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[166]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨166, by decide⟩))

/-- The actual native sparse relation supplies gate 145. -/
theorem gate145 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate145.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate145.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨145, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate145 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[167]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨167, by decide⟩))

/-- The actual native sparse relation supplies gate 146. -/
theorem gate146 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate146.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate146.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨146, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate146 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[168]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨168, by decide⟩))

/-- The actual native sparse relation supplies gate 147. -/
theorem gate147 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate147.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate147.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨147, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate147 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[169]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨169, by decide⟩))

/-- The actual native sparse relation supplies gate 148. -/
theorem gate148 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate148.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate148.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨148, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate148 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[170]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨170, by decide⟩))

/-- The actual native sparse relation supplies gate 149. -/
theorem gate149 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate149.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate149.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨149, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate149 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[171]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨171, by decide⟩))

/-- The actual native sparse relation supplies gate 150. -/
theorem gate150 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate150.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate150.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨150, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate150 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[172]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨172, by decide⟩))

/-- The actual native sparse relation supplies gate 151. -/
theorem gate151 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate151.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate151.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨151, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate151 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[173]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨173, by decide⟩))

/-- The actual native sparse relation supplies gate 152. -/
theorem gate152 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate152.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate152.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨152, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate152 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[174]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨174, by decide⟩))

/-- The actual native sparse relation supplies gate 153. -/
theorem gate153 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate153.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate153.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨153, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate153 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[175]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨175, by decide⟩))

/-- The actual native sparse relation supplies gate 154. -/
theorem gate154 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate154.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate154.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨154, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate154 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[176]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨176, by decide⟩))

/-- The actual native sparse relation supplies gate 155. -/
theorem gate155 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate155.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate155.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨155, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate155 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[177]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨177, by decide⟩))

/-- The actual native sparse relation supplies gate 156. -/
theorem gate156 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate156.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate156.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨156, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate156 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[178]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨178, by decide⟩))

/-- The actual native sparse relation supplies gate 157. -/
theorem gate157 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate157.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate157.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨157, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate157 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[179]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨179, by decide⟩))

/-- The actual native sparse relation supplies gate 158. -/
theorem gate158 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate158.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate158.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨158, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate158 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[180]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨180, by decide⟩))

/-- The actual native sparse relation supplies gate 159. -/
theorem gate159 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate159.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 := by
  have checked : Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate159.check = true :=
    List.all_eq_true.mp Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gatesChecked _ (List.get_mem _ ⟨159, by decide⟩)
  have binding : sparseResidual Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate159 (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) =
      (Clause.gate ((((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.Keccak.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[181]'(by decide)).enforced_relation).residual physical := by kernel_rfl
  exact (sparse_checked checked _).symm.trans
    (binding.trans (gate_at accepted ⟨0, by decide⟩ ⟨181, by decide⟩))

/-- This batch retains every native scalar equation at these positions. -/
theorem gates009 (physical : GKRAddress → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Airbender.Compiler.Captures.Keccak.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate144, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate145, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate146, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate147, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate148, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate149, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate150, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate151, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate152, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate153, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate154, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate155, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate156, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate157, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate158, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate159], gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address) = 0 :=
  (cons_holds (gate144 physical accepted) (cons_holds (gate145 physical accepted) (cons_holds (gate146 physical accepted) (cons_holds (gate147 physical accepted) (cons_holds (gate148 physical accepted) (cons_holds (gate149 physical accepted) (cons_holds (gate150 physical accepted) (cons_holds (gate151 physical accepted) (cons_holds (gate152 physical accepted) (cons_holds (gate153 physical accepted) (cons_holds (gate154 physical accepted) (cons_holds (gate155 physical accepted) (cons_holds (gate156 physical accepted) (cons_holds (gate157 physical accepted) (cons_holds (gate158 physical accepted) (cons_holds (gate159 physical accepted) (by intro gate member; cases member)))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
