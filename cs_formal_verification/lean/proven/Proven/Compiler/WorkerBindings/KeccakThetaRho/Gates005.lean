module
public import Proven.Compiler.WorkerArithmetic.KeccakThetaRho
public import Human.Compiler.Captures.KeccakThetaRho
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakThetaRho.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakThetaRho
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding40 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate40 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate40 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate40.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding40 physical).trans (gate_at accepted ⟨2, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause40 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  exact (binding40 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨40, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding41 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate41 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate41 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate41.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding41 physical).trans (gate_at accepted ⟨3, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause41 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  exact (binding41 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨41, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding42 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate42 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate42 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate42.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding42 physical).trans (gate_at accepted ⟨4, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause42 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  exact (binding42 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨42, by decide⟩)))
theorem gates005 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate40, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate41, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate42], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (by intro gate member; cases member))))

theorem clauses005 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[4]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause40 physical holds) (cons_zero (clause41 physical holds) (cons_zero (clause42 physical holds) (by intro clause member; cases member))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
